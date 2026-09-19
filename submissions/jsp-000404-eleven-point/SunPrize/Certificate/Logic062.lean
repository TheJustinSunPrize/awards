import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step113615 (p2122 p2396 p2608 p2829 p3093 p3918 : Prop)
    (h95271 : p3093 ∨ (¬ p3918) ∨ p2396 ∨ (¬ p2608) ∨ p2122)
    (h96376 : p3918 ∨ p2829)
    : p2829 ∨ p2122 ∨ p2396 ∨ p3093 ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3918) := (Or.elim h95271 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h96376 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113617 (p2177 p2717 p2774 p2829 p3309 p3918 : Prop)
    (h95275 : (¬ p3309) ∨ p2717 ∨ (¬ p2177) ∨ (¬ p2774) ∨ (¬ p3918))
    (h96376 : p3918 ∨ p2829)
    : p2829 ∨ p2717 ∨ (¬ p2177) ∨ (¬ p2774) ∨ (¬ p3309) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3918) := (Or.elim h95275 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h96376 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113618 (p2295 p2696 p2774 p2829 p3309 p3918 : Prop)
    (h95277 : (¬ p3309) ∨ p2696 ∨ (¬ p3918) ∨ (¬ p2774) ∨ p2295)
    (h96376 : p3918 ∨ p2829)
    : p2829 ∨ p2295 ∨ p2696 ∨ (¬ p3309) ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3918) := (Or.elim h95277 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h96376 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113620 (p2166 p2210 p2829 p2860 p3093 p3918 : Prop)
    (h113168 : p2860 ∨ (¬ p2166) ∨ p3093 ∨ (¬ p2210) ∨ (¬ p3918))
    (h96376 : p3918 ∨ p2829)
    : p2829 ∨ p2860 ∨ (¬ p2166) ∨ p3093 ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2860) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3918) := (Or.elim h113168 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h96376 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113622 (p2504 p2598 p2774 p2829 p3016 p3918 p4753 : Prop)
    (h105514 : p4753)
    (h95282 : (¬ p3918) ∨ (¬ p2774) ∨ (¬ p2504) ∨ p2598 ∨ p3016 ∨ (¬ p4753))
    (h96376 : p3918 ∨ p2829)
    : p2829 ∨ (¬ p2774) ∨ (¬ p2504) ∨ p3016 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4753 := h105514;
    let u6 : (¬ p3918) := (Or.elim h95282 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96376 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113625 (p2819 p2829 p3918 p4075 p4452 p4710 p5503 : Prop)
    (h95290 : (¬ p4075) ∨ (¬ p5503) ∨ (¬ p4710) ∨ p2819 ∨ (¬ p3918) ∨ (¬ p4452))
    (h96376 : p3918 ∨ p2829)
    : p2829 ∨ (¬ p5503) ∨ (¬ p4075) ∨ (¬ p4710) ∨ (¬ p4452) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3918) := (Or.elim h95290 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h96376 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113630 (p2440 p2829 p3019 p3918 p4337 p4435 p5514 : Prop)
    (h111312 : p4435 ∨ (¬ p5514) ∨ (¬ p3019) ∨ (¬ p4337) ∨ (¬ p3918) ∨ (¬ p2440))
    (h96376 : p3918 ∨ p2829)
    : p2829 ∨ p4435 ∨ (¬ p5514) ∨ (¬ p3019) ∨ (¬ p4337) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4435) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4337 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3918) := (Or.elim h111312 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96376 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113633 (p2122 p2563 p2829 p2982 p3125 p3319 p3918 : Prop)
    (h112446 : p3125 ∨ (¬ p3918) ∨ p2982 ∨ p2122 ∨ (¬ p3319) ∨ (¬ p2563))
    (h96376 : p3918 ∨ p2829)
    : p2829 ∨ p3125 ∨ p2982 ∨ p2122 ∨ (¬ p3319) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3918) := (Or.elim h112446 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96376 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113634 (p2210 p2373 p2829 p2860 p3093 p3918 p4210 : Prop)
    (h113177 : p2860 ∨ (¬ p2210) ∨ (¬ p2373) ∨ (¬ p4210) ∨ (¬ p3918) ∨ p3093)
    (h96376 : p3918 ∨ p2829)
    : p2829 ∨ p2860 ∨ (¬ p2210) ∨ (¬ p2373) ∨ (¬ p4210) ∨ p3093 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2860) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3918) := (Or.elim h113177 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (u5 r4))))))))))));
    (Or.elim h96376 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113641 (p2088 p2102 p2829 p2860 p3073 p3425 p3918 p4313 p4317 : Prop)
    (h113535 : (¬ p2860) ∨ (¬ p2102) ∨ (¬ p4313) ∨ p2088 ∨ (¬ p3073) ∨ (¬ p3918) ∨ (¬ p4317) ∨ p3425)
    (h96376 : p3918 ∨ p2829)
    : p2829 ∨ (¬ p2860) ∨ (¬ p2102) ∨ (¬ p4313) ∨ p2088 ∨ (¬ p3073) ∨ (¬ p4317) ∨ p3425 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2102 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4317 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p3918) := (Or.elim h113535 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (u7 r6))))))))))))))));
    (Or.elim h96376 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113642 (p2177 p2230 p2373 p2774 p2829 p3309 p3363 p3367 p3918 p4905 : Prop)
    (h105995 : p4905)
    (h81189 : (¬ p3309) ∨ (¬ p4905) ∨ p2230 ∨ (¬ p3918) ∨ (¬ p2177) ∨ p2373 ∨ (¬ p2774) ∨ (¬ p3363) ∨ p3367)
    (h96376 : p3918 ∨ p2829)
    : p2829 ∨ (¬ p2177) ∨ p2230 ∨ (¬ p2774) ∨ p3367 ∨ p2373 ∨ (¬ p3363) ∨ (¬ p3309) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4905 := h105995;
    let u9 : (¬ p3918) := (Or.elim h81189 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (u4 r7))))))))))))))))));
    (Or.elim h96376 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113643 (p2363 p2737 p2774 p2829 p2946 p3063 p3115 p3361 p3918 p5059 : Prop)
    (h83500 : (¬ p2774) ∨ (¬ p3063) ∨ p3115 ∨ (¬ p5059) ∨ (¬ p3361) ∨ p2946 ∨ p2737 ∨ (¬ p3918) ∨ (¬ p2363))
    (h96376 : p3918 ∨ p2829)
    : p2829 ∨ (¬ p2363) ∨ (¬ p3361) ∨ p2737 ∨ (¬ p2774) ∨ (¬ p3063) ∨ p3115 ∨ p2946 ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p3918) := (Or.elim h83500 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (False.elim (r7 u1))))))))))))))))));
    (Or.elim h96376 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113644 (p2363 p2449 p2737 p2774 p2807 p2829 p3063 p3361 p3918 p4669 : Prop)
    (h105415 : p4669)
    (h83503 : (¬ p3063) ∨ p2737 ∨ (¬ p3361) ∨ p2449 ∨ (¬ p2363) ∨ (¬ p2774) ∨ (¬ p4669) ∨ (¬ p3918) ∨ p2807)
    (h96376 : p3918 ∨ p2829)
    : p2829 ∨ (¬ p2774) ∨ (¬ p2363) ∨ p2807 ∨ p2737 ∨ p2449 ∨ (¬ p3063) ∨ (¬ p3361) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4669 := h105415;
    let u9 : (¬ p3918) := (Or.elim h83503 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (False.elim (u3 r7))))))))))))))))));
    (Or.elim h96376 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113645 (p2396 p2737 p2774 p2829 p3166 p3256 p3309 p3361 p3918 p3950 : Prop)
    (h85342 : (¬ p2396) ∨ (¬ p3309) ∨ p3256 ∨ (¬ p3361) ∨ (¬ p2774) ∨ (¬ p3950) ∨ p2737 ∨ (¬ p3918) ∨ p3166)
    (h96376 : p3918 ∨ p2829)
    : p2829 ∨ (¬ p2396) ∨ p3166 ∨ p2737 ∨ p3256 ∨ (¬ p2774) ∨ (¬ p3361) ∨ (¬ p3950) ∨ (¬ p3309) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p3918) := (Or.elim h85342 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u3 q6))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (False.elim (u2 r7))))))))))))))))));
    (Or.elim h96376 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113650 (p2396 p2663 p2774 p2829 p3166 p3256 p3309 p3363 p3367 p3918 p3950 : Prop)
    (h85321 : p3166 ∨ p3256 ∨ (¬ p3918) ∨ (¬ p2663) ∨ p3367 ∨ (¬ p2774) ∨ (¬ p3363) ∨ (¬ p2396) ∨ (¬ p3309) ∨ (¬ p3950))
    (h96376 : p3918 ∨ p2829)
    : p2829 ∨ (¬ p2396) ∨ p3166 ∨ p3367 ∨ (¬ p3309) ∨ p3256 ∨ (¬ p2774) ∨ (¬ p2663) ∨ (¬ p3363) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p3918) := (Or.elim h85321 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h96376 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113651 (p2363 p2737 p2774 p2829 p2946 p3073 p3156 p3361 p3918 p4134 p4317 : Prop)
    (h105379 : p4134)
    (h88523 : (¬ p4317) ∨ p2363 ∨ p2737 ∨ (¬ p3918) ∨ (¬ p3073) ∨ p3156 ∨ p2946 ∨ (¬ p3361) ∨ (¬ p4134) ∨ (¬ p2774))
    (h96376 : p3918 ∨ p2829)
    : p2829 ∨ (¬ p3073) ∨ (¬ p3361) ∨ (¬ p4317) ∨ p2363 ∨ p3156 ∨ (¬ p2774) ∨ p2737 ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4317 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4134 := h105379;
    let u10 : (¬ p3918) := (Or.elim h88523 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u8 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u6))))))))))))))))))));
    (Or.elim h96376 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113657 (p2417 p2608 p2761 p2829 p3093 p3389 p3519 p3918 p4329 p4376 p5254 : Prop)
    (h106320 : p4376)
    (h95285 : (¬ p4329) ∨ (¬ p2608) ∨ (¬ p3389) ∨ (¬ p2761) ∨ (¬ p3519) ∨ (¬ p3918) ∨ p3093 ∨ (¬ p5254) ∨ (¬ p4376) ∨ (¬ p2417))
    (h96376 : p3918 ∨ p2829)
    : p2829 ∨ (¬ p2417) ∨ (¬ p2761) ∨ (¬ p2608) ∨ p3093 ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p4329) ∨ (¬ p5254) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4329 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    let u10 : (¬ p3918) := (Or.elim h95285 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u1))))))))))))))))))));
    (Or.elim h96376 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113660 (p2246 p2459 p2608 p2744 p2807 p2819 p2829 p3093 p3256 p3918 p4044 p4503 : Prop)
    (h106503 : p2744)
    (h106530 : p4503)
    (h95278 : (¬ p2246) ∨ (¬ p4044) ∨ (¬ p3918) ∨ p2819 ∨ p3093 ∨ p2459 ∨ (¬ p2807) ∨ (¬ p2744) ∨ (¬ p2608) ∨ (¬ p3256) ∨ (¬ p4503))
    (h96376 : p3918 ∨ p2829)
    : p2829 ∨ p2819 ∨ (¬ p4044) ∨ (¬ p2807) ∨ p3093 ∨ (¬ p3256) ∨ (¬ p2608) ∨ (¬ p2246) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2744 := h106503;
    let u10 : p4503 := h106530;
    let u11 : (¬ p3918) := (Or.elim h95278 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u8 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u5))) (fun r9 => (False.elim (r9 u10))))))))))))))))))))));
    (Or.elim h96376 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113663 (p2608 p2761 p2829 p3019 p3093 p3266 p3343 p3516 p3543 p3918 p4337 p4697 p4793 : Prop)
    (h105438 : p4793)
    (h95280 : p3266 ∨ (¬ p2761) ∨ (¬ p3516) ∨ (¬ p4697) ∨ (¬ p2608) ∨ p3343 ∨ (¬ p3019) ∨ (¬ p4793) ∨ p3093 ∨ (¬ p3543) ∨ (¬ p4337) ∨ (¬ p3918))
    (h96376 : p3918 ∨ p2829)
    : p2829 ∨ (¬ p3516) ∨ p3343 ∨ (¬ p3543) ∨ (¬ p4697) ∨ (¬ p2761) ∨ p3266 ∨ (¬ p2608) ∨ (¬ p3019) ∨ p3093 ∨ (¬ p4337) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3543 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4337 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4793 := h105438;
    let u12 : (¬ p3918) := (Or.elim h95280 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u9 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u3))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u10))) (fun r10 => r10))))))))))))))))))))));
    (Or.elim h96376 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113667 (p2295 p4112 p4156 p4194 : Prop)
    (h29696 : (¬ p4112) ∨ (¬ p4156) ∨ p4194)
    (h96453 : p4156 ∨ (¬ p2295))
    : (¬ p2295) ∨ p4194 ∨ (¬ p4112) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4194) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4112 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4156) := (Or.elim h29696 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h96453 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113668 (p2295 p2995 p4156 p4336 : Prop)
    (h23993 : p2995 ∨ (¬ p4156) ∨ (¬ p4336))
    (h96453 : p4156 ∨ (¬ p2295))
    : (¬ p2295) ∨ p2995 ∨ (¬ p4336) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2995) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4156) := (Or.elim h23993 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96453 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113669 (p2295 p2641 p2996 p4156 : Prop)
    (h86139 : (¬ p2996) ∨ (¬ p4156) ∨ (¬ p2641))
    (h96453 : p4156 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p2996) ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4156) := (Or.elim h86139 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96453 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113670 (p2295 p2685 p2797 p4156 : Prop)
    (h87125 : (¬ p4156) ∨ (¬ p2797) ∨ p2685)
    (h96453 : p4156 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p2797) ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4156) := (Or.elim h87125 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h96453 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113671 (p2295 p2331 p2807 p4156 : Prop)
    (h90826 : (¬ p4156) ∨ (¬ p2331) ∨ p2807)
    (h96453 : p4156 ∨ (¬ p2295))
    : (¬ p2295) ∨ p2807 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2807) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4156) := (Or.elim h90826 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h96453 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113672 (p2295 p2668 p3931 p4156 p4260 : Prop)
    (h90833 : (¬ p4260) ∨ (¬ p3931) ∨ p2668 ∨ (¬ p4156))
    (h96453 : p4156 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p3931) ∨ (¬ p4260) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4156) := (Or.elim h90833 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => r2))))));
    (Or.elim h96453 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113673 (p2295 p2396 p2449 p2668 p4156 : Prop)
    (h90839 : (¬ p2449) ∨ (¬ p4156) ∨ p2668 ∨ p2396)
    (h96453 : p4156 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p2449) ∨ p2668 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4156) := (Or.elim h90839 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (u3 r2))))))));
    (Or.elim h96453 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113676 (p2295 p2396 p2449 p2553 p4156 p4976 : Prop)
    (h105465 : p4976)
    (h86510 : (¬ p2449) ∨ p2396 ∨ (¬ p4976) ∨ (¬ p4156) ∨ p2553)
    (h96453 : p4156 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p2449) ∨ p2553 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4976 := h105465;
    let u5 : (¬ p4156) := (Or.elim h86510 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h96453 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113677 (p2122 p2295 p2396 p2449 p4156 p4843 : Prop)
    (h105449 : p4843)
    (h86531 : (¬ p2449) ∨ p2396 ∨ p2122 ∨ (¬ p4156) ∨ (¬ p4843))
    (h96453 : p4156 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p2449) ∨ p2396 ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4843 := h105449;
    let u5 : (¬ p4156) := (Or.elim h86531 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96453 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113678 (p2177 p2264 p2295 p2307 p4156 p4581 : Prop)
    (h105405 : p4581)
    (h90825 : (¬ p2264) ∨ (¬ p4156) ∨ p2177 ∨ (¬ p4581) ∨ p2307)
    (h96453 : p4156 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p2264) ∨ p2177 ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4581 := h105405;
    let u5 : (¬ p4156) := (Or.elim h90825 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h96453 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113679 (p2264 p2295 p2881 p3323 p4140 p4156 : Prop)
    (h107313 : (¬ p2264) ∨ p3323 ∨ (¬ p4156) ∨ (¬ p4140) ∨ p2881)
    (h96453 : p4156 ∨ (¬ p2295))
    : (¬ p2295) ∨ p3323 ∨ (¬ p4140) ∨ p2881 ∨ (¬ p2264) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4156) := (Or.elim h107313 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h96453 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113680 (p2177 p2241 p2264 p2295 p2641 p4156 : Prop)
    (h90836 : (¬ p2264) ∨ (¬ p2641) ∨ p2177 ∨ (¬ p4156) ∨ (¬ p2241))
    (h96453 : p4156 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p2641) ∨ (¬ p2241) ∨ p2177 ∨ (¬ p2264) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4156) := (Or.elim h90836 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h96453 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113683 (p2274 p2295 p2449 p3547 p3631 p4156 : Prop)
    (h91726 : (¬ p3547) ∨ (¬ p4156) ∨ (¬ p2449) ∨ p3631 ∨ p2274)
    (h96453 : p4156 ∨ (¬ p2295))
    : (¬ p2295) ∨ p3631 ∨ (¬ p2449) ∨ (¬ p3547) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3631) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3547 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4156) := (Or.elim h91726 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h96453 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113684 (p2177 p2264 p2295 p2630 p2797 p4156 : Prop)
    (h92159 : (¬ p2264) ∨ (¬ p4156) ∨ p2177 ∨ p2630 ∨ (¬ p2797))
    (h96453 : p4156 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p2797) ∨ p2177 ∨ (¬ p2264) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4156) := (Or.elim h92159 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h96453 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113685 (p2177 p2264 p2295 p2737 p2797 p4156 : Prop)
    (h92207 : (¬ p2264) ∨ p2177 ∨ (¬ p4156) ∨ (¬ p2797) ∨ (¬ p2737))
    (h96453 : p4156 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p2797) ∨ (¬ p2264) ∨ p2177 ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4156) := (Or.elim h92207 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96453 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113687 (p2177 p2264 p2295 p2696 p2774 p4156 p4328 : Prop)
    (h76187 : (¬ p2264) ∨ p2177 ∨ (¬ p2774) ∨ (¬ p4328) ∨ p2696 ∨ (¬ p4156))
    (h96453 : p4156 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p4328) ∨ (¬ p2264) ∨ p2696 ∨ p2177 ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4156) := (Or.elim h76187 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => r4))))))))));
    (Or.elim h96453 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113693 (p2177 p2246 p2264 p2295 p2331 p2992 p4156 : Prop)
    (h82381 : p2992 ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p4156) ∨ (¬ p2264) ∨ p2177)
    (h96453 : p4156 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p2246) ∨ p2177 ∨ (¬ p2264) ∨ (¬ p2331) ∨ p2992 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4156) := (Or.elim h82381 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u2 r4))))))))))));
    (Or.elim h96453 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113698 (p2177 p2264 p2295 p2962 p3323 p3654 p4156 : Prop)
    (h90930 : (¬ p3654) ∨ p3323 ∨ (¬ p4156) ∨ p2177 ∨ (¬ p2264) ∨ (¬ p2962))
    (h96453 : p4156 ∨ (¬ p2295))
    : (¬ p2295) ∨ p3323 ∨ (¬ p3654) ∨ p2177 ∨ (¬ p2264) ∨ (¬ p2962) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4156) := (Or.elim h90930 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96453 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113700 (p2177 p2295 p2341 p2396 p2797 p4066 p4156 : Prop)
    (h101375 : (¬ p2396) ∨ (¬ p2341) ∨ (¬ p4066) ∨ p2177 ∨ (¬ p4156) ∨ (¬ p2797))
    (h96453 : p4156 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p2797) ∨ (¬ p2396) ∨ (¬ p2341) ∨ p2177 ∨ (¬ p4066) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4156) := (Or.elim h101375 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h96453 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113720 (p2098 p2177 p2248 p2264 p2295 p2331 p2707 p3537 p3873 p4156 p4477 : Prop)
    (h105365 : p2248)
    (h88383 : p2098 ∨ (¬ p4156) ∨ (¬ p3873) ∨ (¬ p4477) ∨ (¬ p2331) ∨ p2177 ∨ (¬ p3537) ∨ (¬ p2248) ∨ (¬ p2264) ∨ p2707)
    (h96453 : p4156 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p3537) ∨ (¬ p2331) ∨ p2177 ∨ (¬ p2264) ∨ (¬ p4477) ∨ p2707 ∨ p2098 ∨ (¬ p3873) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2248 := h105365;
    let u10 : (¬ p4156) := (Or.elim h88383 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (u6 r8))))))))))))))))))));
    (Or.elim h96453 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113721 (p2177 p2248 p2264 p2295 p2331 p2598 p2707 p3367 p3873 p4156 p4477 : Prop)
    (h105365 : p2248)
    (h88459 : (¬ p2264) ∨ p2177 ∨ p2707 ∨ (¬ p3367) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p4156) ∨ (¬ p4477) ∨ (¬ p3873) ∨ p2598)
    (h96453 : p4156 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p2264) ∨ (¬ p2331) ∨ (¬ p3873) ∨ p2177 ∨ (¬ p4477) ∨ p2598 ∨ (¬ p3367) ∨ p2707 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2248 := h105365;
    let u10 : (¬ p4156) := (Or.elim h88459 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (u6 r8))))))))))))))))))));
    (Or.elim h96453 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113727 (p3083 p4041 p4437 : Prop)
    (h106487 : p4041 ∨ (¬ p4437))
    (h93397 : p4437 ∨ p3083)
    : p3083 ∨ p4041 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4041) := (fun h => hn (Or.inr h));
    let u2 : (¬ p4437) := (Or.elim h106487 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h93397 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113728 (p2528 p3083 p3256 p4437 : Prop)
    (h25758 : p2528 ∨ (¬ p3256) ∨ (¬ p4437))
    (h93397 : p4437 ∨ p3083)
    : p3083 ∨ p2528 ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4437) := (Or.elim h25758 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h93397 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113730 (p2088 p2481 p3083 p3256 p4437 : Prop)
    (h76913 : (¬ p3256) ∨ (¬ p2481) ∨ p2088 ∨ (¬ p4437))
    (h93397 : p4437 ∨ p3083)
    : p3083 ∨ (¬ p2481) ∨ (¬ p3256) ∨ p2088 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : p2481 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4437) := (Or.elim h76913 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => r2))))));
    (Or.elim h93397 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113731 (p2470 p2663 p3083 p3166 p4437 : Prop)
    (h87337 : p3166 ∨ (¬ p2470) ∨ (¬ p4437) ∨ (¬ p2663))
    (h93397 : p4437 ∨ p3083)
    : p3083 ∨ p3166 ∨ (¬ p2470) ∨ (¬ p2663) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4437) := (Or.elim h87337 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h93397 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113732 (p2440 p3083 p3878 p4355 p4437 : Prop)
    (h93674 : (¬ p4437) ∨ (¬ p3878) ∨ p2440 ∨ (¬ p4355))
    (h93397 : p4437 ∨ p3083)
    : p3083 ∨ (¬ p3878) ∨ (¬ p4355) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : p3878 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4437) := (Or.elim h93674 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h93397 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113735 (p2651 p3083 p3166 p3641 p4437 p4753 : Prop)
    (h105514 : p4753)
    (h77420 : p3166 ∨ (¬ p3641) ∨ (¬ p4753) ∨ (¬ p2651) ∨ (¬ p4437))
    (h93397 : p4437 ∨ p3083)
    : p3083 ∨ p3166 ∨ (¬ p2651) ∨ (¬ p3641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4753 := h105514;
    let u5 : (¬ p4437) := (Or.elim h77420 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h93397 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113736 (p2727 p3083 p3189 p3641 p4437 p4753 : Prop)
    (h105514 : p4753)
    (h77424 : p3189 ∨ (¬ p3641) ∨ (¬ p2727) ∨ (¬ p4437) ∨ (¬ p4753))
    (h93397 : p4437 ∨ p3083)
    : p3083 ∨ p3189 ∨ (¬ p3641) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4753 := h105514;
    let u5 : (¬ p4437) := (Or.elim h77424 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h93397 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113738 (p2295 p2331 p3083 p3166 p4432 p4437 : Prop)
    (h79335 : p3166 ∨ (¬ p2295) ∨ (¬ p4437) ∨ (¬ p2331) ∨ (¬ p4432))
    (h93397 : p4437 ∨ p3083)
    : p3083 ∨ (¬ p2295) ∨ (¬ p2331) ∨ p3166 ∨ (¬ p4432) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4437) := (Or.elim h79335 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h93397 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113739 (p2518 p2651 p3083 p3166 p4437 p4814 : Prop)
    (h105440 : p4814)
    (h81502 : (¬ p2518) ∨ p3166 ∨ (¬ p4437) ∨ (¬ p4814) ∨ (¬ p2651))
    (h93397 : p4437 ∨ p3083)
    : p3083 ∨ (¬ p2518) ∨ p3166 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4814 := h105440;
    let u5 : (¬ p4437) := (Or.elim h81502 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h93397 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113740 (p2528 p2651 p2727 p3083 p3189 p4437 : Prop)
    (h82192 : p3189 ∨ (¬ p2727) ∨ p2528 ∨ (¬ p4437) ∨ p2651)
    (h93397 : p4437 ∨ p3083)
    : p3083 ∨ p3189 ∨ p2528 ∨ p2651 ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4437) := (Or.elim h82192 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h93397 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113741 (p2470 p2665 p2727 p3083 p3189 p4437 : Prop)
    (h105373 : p2665)
    (h82288 : p3189 ∨ (¬ p2470) ∨ (¬ p2727) ∨ (¬ p2665) ∨ (¬ p4437))
    (h93397 : p4437 ∨ p3083)
    : p3083 ∨ p3189 ∨ (¬ p2470) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2665 := h105373;
    let u5 : (¬ p4437) := (Or.elim h82288 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h93397 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113743 (p2440 p2727 p3083 p3189 p4437 p4608 : Prop)
    (h105540 : p4608)
    (h82311 : p3189 ∨ (¬ p2727) ∨ (¬ p4437) ∨ p2440 ∨ (¬ p4608))
    (h93397 : p4437 ∨ p3083)
    : p3083 ∨ p3189 ∨ (¬ p2727) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4608 := h105540;
    let u5 : (¬ p4437) := (Or.elim h82311 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h93397 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113744 (p2528 p2630 p2651 p3005 p3083 p4437 : Prop)
    (h86946 : p3005 ∨ p2528 ∨ (¬ p4437) ∨ (¬ p2630) ∨ p2651)
    (h93397 : p4437 ∨ p3083)
    : p3083 ∨ p3005 ∨ p2528 ∨ (¬ p2630) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4437) := (Or.elim h86946 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h93397 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113745 (p2470 p2630 p2665 p3005 p3083 p4437 : Prop)
    (h105373 : p2665)
    (h87067 : p3005 ∨ (¬ p2470) ∨ (¬ p2630) ∨ (¬ p2665) ∨ (¬ p4437))
    (h93397 : p4437 ∨ p3083)
    : p3083 ∨ p3005 ∨ (¬ p2470) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2665 := h105373;
    let u5 : (¬ p4437) := (Or.elim h87067 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h93397 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113748 (p2528 p2651 p2727 p3083 p3166 p4437 : Prop)
    (h100206 : p2528 ∨ p3166 ∨ (¬ p2651) ∨ (¬ p4437) ∨ p2727)
    (h93397 : p4437 ∨ p3083)
    : p3083 ∨ p3166 ∨ p2528 ∨ p2727 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4437) := (Or.elim h100206 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h93397 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113749 (p2528 p2630 p2651 p3083 p3166 p4437 : Prop)
    (h100570 : p2528 ∨ p3166 ∨ (¬ p2651) ∨ (¬ p4437) ∨ p2630)
    (h93397 : p4437 ∨ p3083)
    : p3083 ∨ p3166 ∨ p2630 ∨ (¬ p2651) ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4437) := (Or.elim h100570 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h93397 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113759 (p2563 p3083 p3146 p3256 p4355 p4437 p4509 : Prop)
    (h105392 : p4509)
    (h93677 : (¬ p3256) ∨ p3146 ∨ (¬ p4355) ∨ p2563 ∨ (¬ p4509) ∨ (¬ p4437))
    (h93397 : p4437 ∨ p3083)
    : p3083 ∨ (¬ p4355) ∨ p3146 ∨ (¬ p3256) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : p4355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4509 := h105392;
    let u6 : (¬ p4437) := (Or.elim h93677 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h93397 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113760 (p2630 p2651 p3005 p3083 p4149 p4236 p4437 : Prop)
    (h93877 : p4149 ∨ (¬ p4236) ∨ (¬ p2630) ∨ p3005 ∨ p2651 ∨ (¬ p4437))
    (h93397 : p4437 ∨ p3083)
    : p3083 ∨ p4149 ∨ p3005 ∨ (¬ p4236) ∨ p2651 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4149) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4437) := (Or.elim h93877 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => r4))))))))));
    (Or.elim h93397 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113772 (p2088 p2459 p3005 p3083 p3286 p3755 p4437 p4438 : Prop)
    (h109990 : p3286 ∨ (¬ p2088) ∨ (¬ p3755) ∨ (¬ p4437) ∨ p2459 ∨ (¬ p4438) ∨ p3005)
    (h93397 : p4437 ∨ p3083)
    : p3083 ∨ p3286 ∨ (¬ p2088) ∨ (¬ p3755) ∨ p2459 ∨ (¬ p4438) ∨ p3005 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4437) := (Or.elim h109990 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (u6 r5))))))))))))));
    (Or.elim h93397 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113780 (p2122 p2177 p2245 p2651 p2727 p2774 p3083 p3189 p4437 p4438 p4733 : Prop)
    (h105430 : p4733)
    (h82303 : (¬ p2245) ∨ (¬ p2122) ∨ (¬ p4438) ∨ (¬ p4437) ∨ p3189 ∨ (¬ p2774) ∨ (¬ p2177) ∨ p2651 ∨ (¬ p2727) ∨ (¬ p4733))
    (h93397 : p4437 ∨ p3083)
    : p3083 ∨ (¬ p2774) ∨ p2651 ∨ (¬ p4438) ∨ (¬ p2727) ∨ p3189 ∨ (¬ p2245) ∨ (¬ p2177) ∨ (¬ p2122) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4733 := h105430;
    let u10 : (¬ p4437) := (Or.elim h82303 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u2 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h93397 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113782 (p2132 p2192 p2528 p2663 p3083 p3125 p3166 p3363 p3367 p4330 p4418 p4437 : Prop)
    (h106329 : p4330)
    (h75603 : p3166 ∨ (¬ p3125) ∨ (¬ p2663) ∨ (¬ p2132) ∨ (¬ p4437) ∨ (¬ p2192) ∨ p3367 ∨ (¬ p3363) ∨ (¬ p4330) ∨ (¬ p4418) ∨ p2528)
    (h93397 : p4437 ∨ p3083)
    : p3083 ∨ p3166 ∨ (¬ p3125) ∨ (¬ p2192) ∨ p3367 ∨ (¬ p2132) ∨ p2528 ∨ (¬ p2663) ∨ (¬ p3363) ∨ (¬ p4418) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4330 := h106329;
    let u11 : (¬ p4437) := (Or.elim h75603 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (False.elim (u6 r9))))))))))))))))))))));
    (Or.elim h93397 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113787 (p2396 p2761 p3461 p4623 : Prop)
    (h82504 : p3461 ∨ (¬ p4623) ∨ (¬ p2761))
    (h91159 : p4623 ∨ (¬ p2396))
    : (¬ p2396) ∨ p3461 ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4623) := (Or.elim h82504 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h91159 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113788 (p2396 p2417 p3564 p3581 p4623 : Prop)
    (h19717 : p2417 ∨ (¬ p3564) ∨ (¬ p3581) ∨ (¬ p4623))
    (h91159 : p4623 ∨ (¬ p2396))
    : (¬ p2396) ∨ (¬ p3564) ∨ (¬ p3581) ∨ p2417 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4623) := (Or.elim h19717 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h91159 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113789 (p2396 p3125 p3246 p4204 p4623 : Prop)
    (h84095 : (¬ p4623) ∨ (¬ p3125) ∨ (¬ p4204) ∨ p3246)
    (h91159 : p4623 ∨ (¬ p2396))
    : (¬ p2396) ∨ p3246 ∨ (¬ p4204) ∨ (¬ p3125) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4623) := (Or.elim h84095 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (u1 r2))))))));
    (Or.elim h91159 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113792 (p2274 p2307 p2396 p2761 p3125 p4623 : Prop)
    (h78409 : (¬ p2761) ∨ (¬ p2307) ∨ p2274 ∨ (¬ p4623) ∨ (¬ p3125))
    (h91159 : p4623 ∨ (¬ p2396))
    : (¬ p2396) ∨ (¬ p3125) ∨ p2274 ∨ (¬ p2761) ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4623) := (Or.elim h78409 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h91159 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113794 (p2274 p2396 p2449 p3096 p3564 p4623 : Prop)
    (h79518 : (¬ p3564) ∨ (¬ p4623) ∨ p2274 ∨ (¬ p3096) ∨ p2449)
    (h91159 : p4623 ∨ (¬ p2396))
    : (¬ p2396) ∨ (¬ p3564) ∨ p2274 ∨ p2449 ∨ (¬ p3096) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4623) := (Or.elim h79518 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h91159 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113795 (p2396 p2881 p3246 p3266 p3461 p4623 : Prop)
    (h82486 : p3461 ∨ (¬ p3266) ∨ (¬ p4623) ∨ p3246 ∨ (¬ p2881))
    (h91159 : p4623 ∨ (¬ p2396))
    : (¬ p2396) ∨ p3246 ∨ (¬ p2881) ∨ (¬ p3266) ∨ p3461 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4623) := (Or.elim h82486 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h91159 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113796 (p2274 p2396 p2417 p3125 p4276 p4623 : Prop)
    (h105516 : p4276)
    (h84083 : p2417 ∨ (¬ p4623) ∨ (¬ p3125) ∨ p2274 ∨ (¬ p4276))
    (h91159 : p4623 ∨ (¬ p2396))
    : (¬ p2396) ∨ (¬ p3125) ∨ p2417 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4276 := h105516;
    let u5 : (¬ p4623) := (Or.elim h84083 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h91159 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113799 (p2396 p2761 p3266 p3319 p3923 p4623 : Prop)
    (h84196 : p3266 ∨ (¬ p4623) ∨ (¬ p3319) ∨ (¬ p2761) ∨ (¬ p3923))
    (h91159 : p4623 ∨ (¬ p2396))
    : (¬ p2396) ∨ (¬ p3319) ∨ (¬ p3923) ∨ (¬ p2761) ∨ p3266 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4623) := (Or.elim h84196 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h91159 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113800 (p2295 p2396 p3323 p3434 p4473 p4623 : Prop)
    (h88129 : (¬ p3323) ∨ p3434 ∨ p2295 ∨ (¬ p4623) ∨ (¬ p4473))
    (h91159 : p4623 ∨ (¬ p2396))
    : (¬ p2396) ∨ p3434 ∨ p2295 ∨ (¬ p3323) ∨ (¬ p4473) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3434) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4473 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4623) := (Or.elim h88129 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h91159 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113801 (p2122 p2315 p2396 p3483 p3516 p4623 : Prop)
    (h105368 : p2315)
    (h90236 : (¬ p3483) ∨ (¬ p4623) ∨ p3516 ∨ (¬ p2315) ∨ p2122)
    (h91159 : p4623 ∨ (¬ p2396))
    : (¬ p2396) ∨ (¬ p3483) ∨ p2122 ∨ p3516 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2315 := h105368;
    let u5 : (¬ p4623) := (Or.elim h90236 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h91159 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113802 (p2307 p2396 p3246 p3654 p4556 p4623 : Prop)
    (h105399 : p4556)
    (h90928 : (¬ p4623) ∨ p2307 ∨ (¬ p3654) ∨ p3246 ∨ (¬ p4556))
    (h91159 : p4623 ∨ (¬ p2396))
    : (¬ p2396) ∨ (¬ p3654) ∨ p3246 ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4556 := h105399;
    let u5 : (¬ p4623) := (Or.elim h90928 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h91159 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113803 (p2307 p2396 p2417 p3654 p4276 p4623 : Prop)
    (h105516 : p4276)
    (h90931 : (¬ p4623) ∨ p2307 ∨ p2417 ∨ (¬ p3654) ∨ (¬ p4276))
    (h91159 : p4623 ∨ (¬ p2396))
    : (¬ p2396) ∨ (¬ p3654) ∨ p2417 ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4276 := h105516;
    let u5 : (¬ p4623) := (Or.elim h90931 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h91159 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113804 (p2307 p2396 p2553 p2761 p3654 p4623 : Prop)
    (h90936 : (¬ p3654) ∨ p2307 ∨ (¬ p4623) ∨ (¬ p2553) ∨ (¬ p2761))
    (h91159 : p4623 ∨ (¬ p2396))
    : (¬ p2396) ∨ p2307 ∨ (¬ p2553) ∨ (¬ p3654) ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4623) := (Or.elim h90936 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h91159 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113806 (p2177 p2396 p2553 p3564 p4623 p4668 : Prop)
    (h105414 : p4668)
    (h91287 : (¬ p3564) ∨ (¬ p4623) ∨ (¬ p4668) ∨ p2177 ∨ p2553)
    (h91159 : p4623 ∨ (¬ p2396))
    : (¬ p2396) ∨ p2553 ∨ p2177 ∨ (¬ p3564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4668 := h105414;
    let u5 : (¬ p4623) := (Or.elim h91287 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h91159 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113807 (p2295 p2307 p2396 p2761 p3654 p4623 : Prop)
    (h98297 : (¬ p3654) ∨ p2307 ∨ (¬ p2761) ∨ (¬ p4623) ∨ (¬ p2295))
    (h91159 : p4623 ∨ (¬ p2396))
    : (¬ p2396) ∨ (¬ p3654) ∨ (¬ p2295) ∨ p2307 ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4623) := (Or.elim h98297 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h91159 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113808 (p2295 p2396 p2553 p2761 p3323 p4623 : Prop)
    (h98640 : (¬ p3323) ∨ (¬ p2761) ∨ (¬ p2553) ∨ p2295 ∨ (¬ p4623))
    (h91159 : p4623 ∨ (¬ p2396))
    : (¬ p2396) ∨ (¬ p3323) ∨ p2295 ∨ (¬ p2553) ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4623) := (Or.elim h98640 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => r3))))))));
    (Or.elim h91159 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113811 (p2396 p2459 p3146 p3266 p3461 p4623 : Prop)
    (h112689 : p2459 ∨ (¬ p4623) ∨ (¬ p3266) ∨ p3461 ∨ (¬ p3146))
    (h91159 : p4623 ∨ (¬ p2396))
    : (¬ p2396) ∨ p2459 ∨ (¬ p3266) ∨ p3461 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4623) := (Or.elim h112689 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h91159 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113813 (p2274 p2396 p3564 p3581 p3791 p4623 p5503 : Prop)
    (h64988 : (¬ p2274) ∨ (¬ p3564) ∨ (¬ p3581) ∨ (¬ p3791) ∨ (¬ p4623) ∨ (¬ p5503))
    (h91159 : p4623 ∨ (¬ p2396))
    : (¬ p2396) ∨ (¬ p3791) ∨ (¬ p3581) ∨ (¬ p2274) ∨ (¬ p5503) ∨ (¬ p3564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4623) := (Or.elim h64988 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h91159 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113825 (p2396 p2459 p3256 p3266 p3461 p4041 p4623 : Prop)
    (h112688 : p2459 ∨ (¬ p3256) ∨ p3461 ∨ (¬ p4041) ∨ (¬ p3266) ∨ (¬ p4623))
    (h91159 : p4623 ∨ (¬ p2396))
    : (¬ p2396) ∨ p2459 ∨ (¬ p3256) ∨ p3461 ∨ (¬ p4041) ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4623) := (Or.elim h112688 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h91159 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113829 (p2264 p2274 p2307 p2396 p2449 p3204 p3319 p4623 : Prop)
    (h84203 : p2449 ∨ (¬ p3319) ∨ (¬ p4623) ∨ p2307 ∨ (¬ p2274) ∨ (¬ p3204) ∨ (¬ p2264))
    (h91159 : p4623 ∨ (¬ p2396))
    : (¬ p2396) ∨ p2449 ∨ (¬ p2264) ∨ p2307 ∨ (¬ p2274) ∨ (¬ p3319) ∨ (¬ p3204) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4623) := (Or.elim h84203 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u2))))))))))))));
    (Or.elim h91159 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113834 (p2307 p2396 p2553 p2696 p2781 p3005 p3256 p3564 p3950 p4623 : Prop)
    (h82863 : (¬ p3564) ∨ p2696 ∨ p3256 ∨ p2553 ∨ (¬ p3950) ∨ (¬ p4623) ∨ p3005 ∨ (¬ p2307) ∨ (¬ p2781))
    (h91159 : p4623 ∨ (¬ p2396))
    : (¬ p2396) ∨ (¬ p3564) ∨ p2696 ∨ (¬ p2307) ∨ p2553 ∨ p3005 ∨ p3256 ∨ (¬ p3950) ∨ (¬ p2781) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p4623) := (Or.elim h82863 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u8))))))))))))))))));
    (Or.elim h91159 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113838 (p2132 p2295 p2307 p2396 p2619 p3146 p3323 p3366 p3950 p4623 p4866 p5016 : Prop)
    (h106063 : p4866)
    (h84766 : (¬ p5016) ∨ p2132 ∨ (¬ p2307) ∨ (¬ p3366) ∨ (¬ p3323) ∨ p3146 ∨ p2295 ∨ (¬ p3950) ∨ (¬ p4866) ∨ (¬ p4623) ∨ p2619)
    (h91159 : p4623 ∨ (¬ p2396))
    : (¬ p2396) ∨ (¬ p3323) ∨ p2132 ∨ (¬ p2307) ∨ p3146 ∨ p2295 ∨ p2619 ∨ (¬ p3366) ∨ (¬ p5016) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4866 := h106063;
    let u11 : (¬ p4623) := (Or.elim h84766 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => q9) (fun r9 => (False.elim (u6 r9))))))))))))))))))))));
    (Or.elim h91159 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113840 (p2396 p2651 p2727 p2996 p3266 p3286 p3343 p3461 p3631 p4450 p4623 p4952 : Prop)
    (h111286 : (¬ p3343) ∨ p2996 ∨ (¬ p4623) ∨ (¬ p3266) ∨ p2651 ∨ (¬ p2727) ∨ p3461 ∨ (¬ p3286) ∨ p3631 ∨ (¬ p4952) ∨ (¬ p4450))
    (h91159 : p4623 ∨ (¬ p2396))
    : (¬ p2396) ∨ (¬ p3343) ∨ p2996 ∨ (¬ p3266) ∨ p2651 ∨ (¬ p2727) ∨ p3461 ∨ (¬ p3286) ∨ p3631 ∨ (¬ p4952) ∨ (¬ p4450) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p4623) := (Or.elim h111286 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u8 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (False.elim (r9 u10))))))))))))))))))))));
    (Or.elim h91159 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113842 (p2274 p2307 p2396 p2696 p2962 p3005 p3125 p3256 p3366 p3370 p3950 p4377 p4623 : Prop)
    (h106170 : p4377)
    (h78396 : p3256 ∨ (¬ p3370) ∨ p2274 ∨ (¬ p4623) ∨ (¬ p4377) ∨ (¬ p3366) ∨ (¬ p2307) ∨ p2696 ∨ p3005 ∨ (¬ p3125) ∨ (¬ p3950) ∨ (¬ p2962))
    (h91159 : p4623 ∨ (¬ p2396))
    : (¬ p2396) ∨ p3256 ∨ (¬ p3366) ∨ p2696 ∨ (¬ p3125) ∨ p3005 ∨ (¬ p2307) ∨ p2274 ∨ (¬ p2962) ∨ (¬ p3370) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4377 := h106170;
    let u12 : (¬ p4623) := (Or.elim h78396 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u5 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u4))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u10))) (fun r10 => (False.elim (r10 u8))))))))))))))))))))))));
    (Or.elim h91159 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113845 (p2252 p2396 p2573 p2750 p2753 p3266 p3286 p3333 p3362 p3422 p3950 p4331 p4623 p5284 : Prop)
    (h106345 : p2750)
    (h95634 : (¬ p5284) ∨ (¬ p3266) ∨ (¬ p3950) ∨ (¬ p2750) ∨ (¬ p3362) ∨ (¬ p3333) ∨ (¬ p2573) ∨ (¬ p2753) ∨ (¬ p4331) ∨ (¬ p4623) ∨ p3286 ∨ p3422 ∨ (¬ p2252))
    (h91159 : p4623 ∨ (¬ p2396))
    : (¬ p2396) ∨ (¬ p5284) ∨ (¬ p3362) ∨ (¬ p3266) ∨ p3286 ∨ (¬ p2573) ∨ p3422 ∨ (¬ p2753) ∨ (¬ p2252) ∨ (¬ p3333) ∨ (¬ p3950) ∨ (¬ p4331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p2750 := h106345;
    let u13 : (¬ p4623) := (Or.elim h95634 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => q9) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (u4 q10))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (u6 q11))) (fun r11 => (False.elim (r11 u8))))))))))))))))))))))))));
    (Or.elim h91159 (fun q0 => (False.elim (u13 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113847 (p2459 p2528 p4404 p4440 : Prop)
    (h112469 : p2528 ∨ (¬ p4440) ∨ (¬ p4404) ∨ (¬ p2459))
    (h102553 : p4440 ∨ p2528)
    : p2528 ∨ (¬ p4404) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p4404 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4440) := (Or.elim h112469 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h102553 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113848 (p2088 p2475 p2528 p4440 : Prop)
    (h112470 : p2528 ∨ (¬ p4440) ∨ (¬ p2088) ∨ (¬ p2475))
    (h102553 : p4440 ∨ p2528)
    : p2528 ∨ (¬ p2088) ∨ (¬ p2475) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4440) := (Or.elim h112470 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h102553 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113849 (p2295 p3032 p3552 p4427 : Prop)
    (h32019 : p3032 ∨ (¬ p3552) ∨ (¬ p4427))
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ p3032 ∨ (¬ p4427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3032) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3552) := (Or.elim h32019 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96452 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113850 (p2295 p2396 p2449 p3552 : Prop)
    (h6739 : (¬ p2396) ∨ p2449 ∨ (¬ p3552))
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p2396) ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3552) := (Or.elim h6739 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h96452 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113851 (p2177 p2264 p2295 p3552 : Prop)
    (h76676 : (¬ p3552) ∨ (¬ p2177) ∨ p2264)
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p2177) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3552) := (Or.elim h76676 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h96452 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113853 (p2295 p3552 p4325 p4475 : Prop)
    (h37091 : (¬ p3552) ∨ (¬ p4325) ∨ p4475)
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ p4475 ∨ (¬ p4325) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4475) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3552) := (Or.elim h37091 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h96452 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113854 (p2295 p2331 p2668 p2807 p3552 : Prop)
    (h76668 : (¬ p3552) ∨ p2331 ∨ p2668 ∨ (¬ p2807))
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ p2331 ∨ p2668 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3552) := (Or.elim h76668 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113856 (p2295 p2331 p2807 p3323 p3552 : Prop)
    (h107112 : (¬ p2807) ∨ p3323 ∨ (¬ p3552) ∨ p2331)
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ p3323 ∨ p2331 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3552) := (Or.elim h107112 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113857 (p2295 p2685 p2797 p3323 p3552 : Prop)
    (h107113 : p3323 ∨ p2797 ∨ (¬ p3552) ∨ (¬ p2685))
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ p3323 ∨ (¬ p2685) ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3552) := (Or.elim h107113 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113858 (p2274 p2295 p2331 p2807 p3552 : Prop)
    (h76674 : (¬ p3552) ∨ p2331 ∨ p2274 ∨ (¬ p2807))
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ p2274 ∨ p2331 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3552) := (Or.elim h76674 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113859 (p2274 p2295 p2641 p2996 p3552 : Prop)
    (h76680 : p2641 ∨ (¬ p3552) ∨ p2274 ∨ p2996)
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ p2996 ∨ p2274 ∨ p2641 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3552) := (Or.elim h76680 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (u1 r2))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113860 (p2295 p2641 p2996 p3323 p3552 : Prop)
    (h107131 : p2641 ∨ p3323 ∨ (¬ p3552) ∨ p2996)
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ p3323 ∨ p2641 ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3552) := (Or.elim h107131 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (u3 r2))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113861 (p2177 p2295 p2717 p3552 p4325 : Prop)
    (h87517 : (¬ p3552) ∨ p2717 ∨ (¬ p4325) ∨ (¬ p2177))
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p4325) ∨ (¬ p2177) ∨ p2717 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3552) := (Or.elim h87517 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113862 (p2295 p2553 p2685 p2797 p3552 p4976 : Prop)
    (h105465 : p4976)
    (h76661 : p2797 ∨ (¬ p3552) ∨ p2553 ∨ (¬ p4976) ∨ (¬ p2685))
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p2685) ∨ p2797 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4976 := h105465;
    let u5 : (¬ p3552) := (Or.elim h76661 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113863 (p2295 p2331 p2553 p2807 p3552 p4976 : Prop)
    (h105465 : p4976)
    (h76662 : (¬ p3552) ∨ p2331 ∨ (¬ p2807) ∨ p2553 ∨ (¬ p4976))
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ p2331 ∨ (¬ p2807) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4976 := h105465;
    let u5 : (¬ p3552) := (Or.elim h76662 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113865 (p2122 p2295 p2331 p2807 p3552 p4843 : Prop)
    (h105449 : p4843)
    (h76665 : (¬ p3552) ∨ p2331 ∨ (¬ p4843) ∨ (¬ p2807) ∨ p2122)
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ p2331 ∨ p2122 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4843 := h105449;
    let u5 : (¬ p3552) := (Or.elim h76665 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113866 (p2295 p2331 p2807 p3309 p3552 p4757 : Prop)
    (h76666 : p2331 ∨ (¬ p3552) ∨ (¬ p4757) ∨ p3309 ∨ (¬ p2807))
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ p3309 ∨ p2331 ∨ (¬ p2807) ∨ (¬ p4757) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3309) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4757 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3552) := (Or.elim h76666 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113867 (p2295 p2383 p2641 p2667 p2996 p3552 : Prop)
    (h76670 : p2641 ∨ p2996 ∨ (¬ p3552) ∨ p2383 ∨ (¬ p2667))
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ p2996 ∨ p2641 ∨ p2383 ∨ (¬ p2667) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3552) := (Or.elim h76670 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113869 (p2295 p2553 p2641 p2996 p3552 p4976 : Prop)
    (h105465 : p4976)
    (h76678 : (¬ p3552) ∨ p2553 ∨ p2996 ∨ (¬ p4976) ∨ p2641)
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ p2996 ∨ p2553 ∨ p2641 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4976 := h105465;
    let u5 : (¬ p3552) := (Or.elim h76678 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113870 (p2295 p2307 p2641 p2996 p3552 p4581 : Prop)
    (h105405 : p4581)
    (h76681 : (¬ p3552) ∨ p2307 ∨ p2641 ∨ p2996 ∨ (¬ p4581))
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ p2307 ∨ p2996 ∨ p2641 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4581 := h105405;
    let u5 : (¬ p3552) := (Or.elim h76681 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113872 (p2295 p2553 p2651 p2727 p2996 p3552 : Prop)
    (h81975 : (¬ p3552) ∨ p2553 ∨ p2996 ∨ (¬ p2651) ∨ p2727)
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ p2553 ∨ (¬ p2651) ∨ p2727 ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3552) := (Or.elim h81975 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113874 (p2177 p2295 p2459 p2685 p2797 p3552 : Prop)
    (h88967 : p2797 ∨ (¬ p3552) ∨ (¬ p2685) ∨ (¬ p2459) ∨ (¬ p2177))
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p2685) ∨ (¬ p2459) ∨ p2797 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3552) := (Or.elim h88967 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113875 (p2177 p2295 p2331 p2685 p2797 p3552 : Prop)
    (h89137 : p2797 ∨ (¬ p2331) ∨ (¬ p3552) ∨ (¬ p2177) ∨ (¬ p2685))
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p2177) ∨ (¬ p2685) ∨ (¬ p2331) ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3552) := (Or.elim h89137 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113879 (p2122 p2295 p2641 p2996 p3552 p4843 : Prop)
    (h105449 : p4843)
    (h97913 : p2641 ∨ (¬ p3552) ∨ p2996 ∨ p2122 ∨ (¬ p4843))
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ p2122 ∨ p2641 ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4843 := h105449;
    let u5 : (¬ p3552) := (Or.elim h97913 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113880 (p2264 p2295 p2307 p2383 p3552 p4133 : Prop)
    (h105712 : p4133)
    (h98304 : (¬ p2383) ∨ p2307 ∨ p2264 ∨ (¬ p4133) ∨ (¬ p3552))
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p2383) ∨ p2307 ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4133 := h105712;
    let u5 : (¬ p3552) := (Or.elim h98304 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113886 (p2274 p2295 p2331 p2685 p2797 p3552 p4117 : Prop)
    (h100740 : p2797 ∨ p2274 ∨ (¬ p2685) ∨ (¬ p2331) ∨ (¬ p4117) ∨ (¬ p3552))
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p2685) ∨ (¬ p4117) ∨ p2274 ∨ (¬ p2331) ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3552) := (Or.elim h100740 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => r4))))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113887 (p2295 p2331 p2807 p3309 p3552 p4024 p4843 : Prop)
    (h105449 : p4843)
    (h101122 : (¬ p4024) ∨ (¬ p3552) ∨ (¬ p4843) ∨ p2331 ∨ (¬ p2807) ∨ p3309)
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ p3309 ∨ p2331 ∨ (¬ p2807) ∨ (¬ p4024) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3309) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4024 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4843 := h105449;
    let u6 : (¬ p3552) := (Or.elim h101122 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u1 r4))))))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113888 (p2295 p2352 p2449 p3276 p3552 p4422 p5284 : Prop)
    (h110910 : p2449 ∨ (¬ p5284) ∨ (¬ p3552) ∨ (¬ p3276) ∨ p2352 ∨ (¬ p4422))
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ p2449 ∨ (¬ p5284) ∨ (¬ p3276) ∨ p2352 ∨ (¬ p4422) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3552) := (Or.elim h110910 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113889 (p2295 p2383 p2449 p3552 p3767 p4036 p5284 : Prop)
    (h110913 : p2449 ∨ (¬ p3767) ∨ (¬ p3552) ∨ (¬ p5284) ∨ p2383 ∨ (¬ p4036))
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ p2449 ∨ (¬ p3767) ∨ (¬ p5284) ∨ p2383 ∨ (¬ p4036) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4036 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3552) := (Or.elim h110913 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113899 (p2122 p2274 p2295 p2341 p2717 p3552 p4155 p4401 : Prop)
    (h111341 : (¬ p2122) ∨ (¬ p2717) ∨ p2341 ∨ (¬ p4401) ∨ p2274 ∨ (¬ p3552) ∨ (¬ p4155))
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p2122) ∨ (¬ p2717) ∨ p2341 ∨ (¬ p4401) ∨ p2274 ∨ (¬ p4155) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4401 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p3552) := (Or.elim h111341 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (r5 u6))))))))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113906 (p2295 p2396 p2417 p2696 p2742 p2996 p3276 p3367 p3552 p3670 p5158 : Prop)
    (h112994 : (¬ p2417) ∨ (¬ p2396) ∨ p3670 ∨ p3367 ∨ p2996 ∨ (¬ p2696) ∨ (¬ p3276) ∨ (¬ p2742) ∨ (¬ p3552) ∨ (¬ p5158))
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p2417) ∨ (¬ p2396) ∨ p3670 ∨ p3367 ∨ p2996 ∨ (¬ p2696) ∨ (¬ p3276) ∨ (¬ p2742) ∨ (¬ p5158) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3670) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5158 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p3552) := (Or.elim h112994 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => q8) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113908 (p2210 p2252 p2264 p2295 p2307 p2459 p2608 p2750 p2972 p3552 p3983 p4450 : Prop)
    (h106345 : p2750)
    (h91867 : (¬ p2972) ∨ p2608 ∨ (¬ p2210) ∨ p2307 ∨ (¬ p2252) ∨ (¬ p2750) ∨ p2264 ∨ (¬ p3983) ∨ p2459 ∨ (¬ p4450) ∨ (¬ p3552))
    (h96452 : p3552 ∨ (¬ p2295))
    : (¬ p2295) ∨ p2264 ∨ p2307 ∨ (¬ p2210) ∨ p2459 ∨ p2608 ∨ (¬ p2252) ∨ (¬ p2972) ∨ (¬ p3983) ∨ (¬ p4450) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2264) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3983 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2750 := h106345;
    let u11 : (¬ p3552) := (Or.elim h91867 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u1 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u4 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => r9))))))))))))))))))));
    (Or.elim h96452 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step113911 (p2797 p3323 p3917 p4337 : Prop)
    (h93205 : p3917 ∨ (¬ p4337) ∨ p3323)
    (h90912 : p4337 ∨ p2797)
    : p2797 ∨ p3917 ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3917) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4337) := (Or.elim h93205 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h90912 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113912 (p2668 p2797 p2819 p4337 : Prop)
    (h98593 : (¬ p4337) ∨ (¬ p2819) ∨ p2668)
    (h90912 : p4337 ∨ p2797)
    : p2797 ∨ p2668 ∨ (¬ p2819) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2668) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4337) := (Or.elim h98593 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h90912 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113913 (p2122 p2295 p2797 p4337 : Prop)
    (h98653 : (¬ p4337) ∨ (¬ p2122) ∨ p2295)
    (h90912 : p4337 ∨ p2797)
    : p2797 ∨ p2295 ∨ (¬ p2122) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4337) := (Or.elim h98653 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h90912 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113915 (p2331 p2774 p2797 p4117 p4337 : Prop)
    (h100759 : (¬ p4337) ∨ p2774 ∨ (¬ p2331) ∨ (¬ p4117))
    (h90912 : p4337 ∨ p2797)
    : p2797 ∨ (¬ p2331) ∨ (¬ p4117) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4337) := (Or.elim h100759 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h90912 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113917 (p2696 p2774 p2797 p3323 p3461 p4337 : Prop)
    (h86366 : p3461 ∨ (¬ p4337) ∨ p3323 ∨ p2774 ∨ (¬ p2696))
    (h90912 : p4337 ∨ p2797)
    : p2797 ∨ p3461 ∨ p2774 ∨ (¬ p2696) ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4337) := (Or.elim h86366 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h90912 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113918 (p2641 p2696 p2751 p2774 p2797 p4337 : Prop)
    (h106343 : p2751)
    (h86408 : p2774 ∨ (¬ p2641) ∨ (¬ p4337) ∨ (¬ p2751) ∨ (¬ p2696))
    (h90912 : p4337 ∨ p2797)
    : p2797 ∨ (¬ p2696) ∨ (¬ p2641) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2751 := h106343;
    let u5 : (¬ p4337) := (Or.elim h86408 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h90912 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113919 (p2696 p2727 p2742 p2774 p2797 p4337 : Prop)
    (h107281 : p2774 ∨ (¬ p2696) ∨ (¬ p2727) ∨ (¬ p2742) ∨ (¬ p4337))
    (h90912 : p4337 ∨ p2797)
    : p2797 ∨ (¬ p2727) ∨ (¬ p2696) ∨ (¬ p2742) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4337) := (Or.elim h107281 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h90912 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113921 (p2098 p2641 p2727 p2774 p2797 p4337 : Prop)
    (h86421 : (¬ p2098) ∨ p2774 ∨ (¬ p4337) ∨ p2727 ∨ (¬ p2641))
    (h90912 : p4337 ∨ p2797)
    : p2797 ∨ (¬ p2098) ∨ p2727 ∨ p2774 ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4337) := (Or.elim h86421 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h90912 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113922 (p2274 p2295 p2696 p2774 p2797 p4337 : Prop)
    (h86454 : p2774 ∨ (¬ p4337) ∨ (¬ p2696) ∨ (¬ p2274) ∨ p2295)
    (h90912 : p4337 ∨ p2797)
    : p2797 ∨ p2295 ∨ p2774 ∨ (¬ p2274) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4337) := (Or.elim h86454 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h90912 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113924 (p2363 p2668 p2737 p2797 p2829 p4337 : Prop)
    (h90467 : (¬ p4337) ∨ p2363 ∨ p2829 ∨ p2668 ∨ (¬ p2737))
    (h90912 : p4337 ∨ p2797)
    : p2797 ∨ p2829 ∨ p2668 ∨ (¬ p2737) ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4337) := (Or.elim h90467 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h90912 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113926 (p2274 p2295 p2737 p2797 p2829 p4337 : Prop)
    (h90522 : (¬ p4337) ∨ p2295 ∨ p2829 ∨ (¬ p2737) ∨ (¬ p2274))
    (h90912 : p4337 ∨ p2797)
    : p2797 ∨ p2295 ∨ (¬ p2737) ∨ (¬ p2274) ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4337) := (Or.elim h90522 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h90912 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113927 (p2563 p2797 p3323 p3914 p4337 p4393 : Prop)
    (h96103 : (¬ p3914) ∨ (¬ p4393) ∨ (¬ p4337) ∨ p2563 ∨ p3323)
    (h90912 : p4337 ∨ p2797)
    : p2797 ∨ (¬ p4393) ∨ p3323 ∨ p2563 ∨ (¬ p3914) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3914 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4337) := (Or.elim h96103 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h90912 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113929 (p2331 p2737 p2797 p2829 p4337 p4790 : Prop)
    (h106424 : p4790)
    (h100391 : (¬ p4337) ∨ p2829 ∨ (¬ p2331) ∨ (¬ p2737) ∨ (¬ p4790))
    (h90912 : p4337 ∨ p2797)
    : p2797 ∨ p2829 ∨ (¬ p2331) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4790 := h106424;
    let u5 : (¬ p4337) := (Or.elim h100391 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h90912 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113932 (p2295 p2696 p2737 p2797 p2829 p3873 p4337 : Prop)
    (h90528 : (¬ p4337) ∨ p2696 ∨ (¬ p2737) ∨ (¬ p3873) ∨ p2829 ∨ p2295)
    (h90912 : p4337 ∨ p2797)
    : p2797 ∨ p2829 ∨ p2295 ∨ (¬ p3873) ∨ p2696 ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4337) := (Or.elim h90528 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (False.elim (u2 r4))))))))))));
    (Or.elim h90912 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113933 (p2132 p2619 p2774 p2797 p3745 p4337 p4509 : Prop)
    (h105392 : p4509)
    (h90635 : (¬ p4337) ∨ (¬ p3745) ∨ (¬ p2132) ∨ (¬ p2619) ∨ p2774 ∨ (¬ p4509))
    (h90912 : p4337 ∨ p2797)
    : p2797 ∨ (¬ p2619) ∨ (¬ p3745) ∨ (¬ p2132) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4509 := h105392;
    let u6 : (¬ p4337) := (Or.elim h90635 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h90912 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113939 (p2440 p2797 p2829 p3019 p4337 p4435 p5514 : Prop)
    (h113630 : p2829 ∨ p4435 ∨ (¬ p5514) ∨ (¬ p3019) ∨ (¬ p4337) ∨ (¬ p2440))
    (h90912 : p4337 ∨ p2797)
    : p2797 ∨ p2829 ∨ p4435 ∨ (¬ p5514) ∨ (¬ p3019) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p4435) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4337) := (Or.elim h113630 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h90912 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113947 (p2427 p2797 p2819 p3323 p3631 p3707 p4337 p4909 p5284 : Prop)
    (h111016 : p3323 ∨ (¬ p3631) ∨ (¬ p5284) ∨ (¬ p3707) ∨ (¬ p4337) ∨ (¬ p2427) ∨ (¬ p4909) ∨ (¬ p2819))
    (h90912 : p4337 ∨ p2797)
    : p2797 ∨ p3323 ∨ (¬ p3631) ∨ (¬ p5284) ∨ (¬ p3707) ∨ (¬ p2427) ∨ (¬ p4909) ∨ (¬ p2819) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4909 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4337) := (Or.elim h111016 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h90912 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113960 (p2608 p2761 p2797 p2829 p3019 p3093 p3266 p3343 p3516 p3543 p4337 p4697 : Prop)
    (h113663 : p2829 ∨ (¬ p3516) ∨ p3343 ∨ (¬ p3543) ∨ (¬ p4697) ∨ (¬ p2761) ∨ p3266 ∨ (¬ p2608) ∨ (¬ p3019) ∨ p3093 ∨ (¬ p4337))
    (h90912 : p4337 ∨ p2797)
    : p2797 ∨ p2829 ∨ (¬ p3516) ∨ p3343 ∨ (¬ p3543) ∨ (¬ p4697) ∨ (¬ p2761) ∨ p3266 ∨ (¬ p2608) ∨ (¬ p3019) ∨ p3093 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3543 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p4337) := (Or.elim h113663 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u10 q9))) (fun r9 => r9))))))))))))))))))));
    (Or.elim h90912 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113971 (p2437 p2651 p2807 p4112 : Prop)
    (h74850 : p2651 ∨ (¬ p4112) ∨ (¬ p2807))
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ (¬ p2807) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4112) := (Or.elim h74850 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h96077 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113972 (p2437 p2727 p2996 p4112 : Prop)
    (h81952 : p2996 ∨ (¬ p4112) ∨ p2727)
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ p2996 ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4112) := (Or.elim h81952 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h96077 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113973 (p2437 p2630 p2685 p4112 : Prop)
    (h87500 : p2630 ∨ (¬ p4112) ∨ (¬ p2685))
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ (¬ p2685) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4112) := (Or.elim h87500 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h96077 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113974 (p2295 p2437 p4112 p4194 : Prop)
    (h113667 : (¬ p2295) ∨ p4194 ∨ (¬ p4112))
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ (¬ p2295) ∨ p4194 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p4194) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4112) := (Or.elim h113667 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h96077 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113975 (p2437 p3016 p3740 p3920 p4112 : Prop)
    (h25297 : (¬ p3016) ∨ (¬ p3740) ∨ (¬ p3920) ∨ (¬ p4112))
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ (¬ p3016) ∨ (¬ p3920) ∨ (¬ p3740) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3920 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4112) := (Or.elim h25297 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h96077 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113979 (p2417 p2437 p2440 p2449 p4112 p4644 : Prop)
    (h105411 : p4644)
    (h74555 : p2449 ∨ (¬ p2417) ∨ (¬ p4112) ∨ p2440 ∨ (¬ p4644))
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ (¬ p2417) ∨ p2449 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4644 := h105411;
    let u5 : (¬ p4112) := (Or.elim h74555 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96077 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113980 (p2264 p2437 p2440 p2911 p4112 p4644 : Prop)
    (h105411 : p4644)
    (h74565 : (¬ p2911) ∨ p2440 ∨ p2264 ∨ (¬ p4644) ∨ (¬ p4112))
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ (¬ p2911) ∨ p2264 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4644 := h105411;
    let u5 : (¬ p4112) := (Or.elim h74565 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h96077 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113982 (p2264 p2437 p2665 p2911 p3389 p4112 : Prop)
    (h105373 : p2665)
    (h74852 : (¬ p2911) ∨ (¬ p3389) ∨ (¬ p4112) ∨ p2264 ∨ (¬ p2665))
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ (¬ p3389) ∨ (¬ p2911) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2665 := h105373;
    let u5 : (¬ p4112) := (Or.elim h74852 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96077 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113983 (p2437 p2665 p3389 p3868 p4112 p4391 : Prop)
    (h105373 : p2665)
    (h49144 : (¬ p2665) ∨ (¬ p3389) ∨ (¬ p3868) ∨ (¬ p4112) ∨ (¬ p4391))
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ (¬ p4391) ∨ (¬ p3868) ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2665 := h105373;
    let u5 : (¬ p4112) := (Or.elim h49144 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h96077 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113984 (p2417 p2437 p2449 p2665 p3389 p4112 : Prop)
    (h105373 : p2665)
    (h74853 : (¬ p2417) ∨ (¬ p3389) ∨ p2449 ∨ (¬ p2665) ∨ (¬ p4112))
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ (¬ p2417) ∨ p2449 ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2665 := h105373;
    let u5 : (¬ p4112) := (Or.elim h74853 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h96077 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113985 (p2264 p2437 p2992 p3038 p3527 p4112 : Prop)
    (h76747 : (¬ p3527) ∨ (¬ p3038) ∨ p2264 ∨ p2992 ∨ (¬ p4112))
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ (¬ p3038) ∨ p2264 ∨ (¬ p3527) ∨ p2992 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p3038 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4112) := (Or.elim h76747 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => r3))))))));
    (Or.elim h96077 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113986 (p2264 p2437 p2911 p3201 p4112 p4753 : Prop)
    (h105514 : p4753)
    (h77171 : (¬ p2911) ∨ (¬ p3201) ∨ p2264 ∨ (¬ p4753) ∨ (¬ p4112))
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ (¬ p2911) ∨ p2264 ∨ (¬ p3201) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4753 := h105514;
    let u5 : (¬ p4112) := (Or.elim h77171 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h96077 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113987 (p2417 p2437 p2449 p3201 p4112 p4753 : Prop)
    (h105514 : p4753)
    (h77228 : (¬ p2417) ∨ (¬ p3201) ∨ (¬ p4112) ∨ (¬ p4753) ∨ p2449)
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ p2449 ∨ (¬ p2417) ∨ (¬ p3201) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4753 := h105514;
    let u5 : (¬ p4112) := (Or.elim h77228 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h96077 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113988 (p2373 p2427 p2437 p4112 p4129 p4391 : Prop)
    (h80282 : (¬ p4129) ∨ (¬ p4112) ∨ p2373 ∨ (¬ p4391) ∨ (¬ p2427))
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ (¬ p4391) ∨ (¬ p4129) ∨ p2373 ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4129 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4112) := (Or.elim h80282 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96077 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113989 (p2264 p2437 p2911 p2922 p4112 p4814 : Prop)
    (h105440 : p4814)
    (h88854 : (¬ p2911) ∨ (¬ p2922) ∨ (¬ p4814) ∨ p2264 ∨ (¬ p4112))
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ (¬ p2922) ∨ (¬ p2911) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4814 := h105440;
    let u5 : (¬ p4112) := (Or.elim h88854 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => r3))))))));
    (Or.elim h96077 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113990 (p2437 p2449 p2992 p3038 p3631 p4112 : Prop)
    (h89342 : (¬ p3631) ∨ p2449 ∨ (¬ p4112) ∨ (¬ p3038) ∨ p2992)
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ (¬ p3631) ∨ (¬ p3038) ∨ p2449 ∨ p2992 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3038 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4112) := (Or.elim h89342 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h96077 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113994 (p2177 p2264 p2437 p2573 p3016 p4112 : Prop)
    (h99420 : (¬ p2177) ∨ (¬ p3016) ∨ (¬ p4112) ∨ p2264 ∨ p2573)
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ (¬ p2177) ∨ p2573 ∨ p2264 ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4112) := (Or.elim h99420 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h96077 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113995 (p2417 p2437 p2449 p2727 p2911 p4112 : Prop)
    (h100130 : p2449 ∨ (¬ p2417) ∨ (¬ p4112) ∨ p2911 ∨ p2727)
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ (¬ p2417) ∨ p2449 ∨ p2727 ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4112) := (Or.elim h100130 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h96077 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113996 (p2437 p2449 p2707 p2737 p3434 p4112 : Prop)
    (h100180 : (¬ p3434) ∨ p2449 ∨ (¬ p4112) ∨ p2737 ∨ (¬ p2707))
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ (¬ p3434) ∨ (¬ p2707) ∨ p2737 ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4112) := (Or.elim h100180 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h96077 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step113998 (p2341 p2437 p2440 p2911 p4112 p4155 p4644 : Prop)
    (h105411 : p4644)
    (h74586 : (¬ p4112) ∨ p2440 ∨ (¬ p4155) ∨ p2341 ∨ (¬ p4644) ∨ (¬ p2911))
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ p2341 ∨ (¬ p2911) ∨ (¬ p4155) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4644 := h105411;
    let u6 : (¬ p4112) := (Or.elim h74586 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h96077 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114006 (p2417 p2437 p2449 p2850 p3741 p4112 p4753 : Prop)
    (h105514 : p4753)
    (h87874 : (¬ p2417) ∨ (¬ p2850) ∨ (¬ p3741) ∨ p2449 ∨ (¬ p4112) ∨ (¬ p4753))
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ (¬ p2417) ∨ (¬ p2850) ∨ p2449 ∨ (¬ p3741) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4753 := h105514;
    let u6 : (¬ p4112) := (Or.elim h87874 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96077 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114009 (p2437 p3016 p3741 p3868 p4112 p4391 p4717 : Prop)
    (h105424 : p4717)
    (h61630 : (¬ p3016) ∨ (¬ p3741) ∨ (¬ p3868) ∨ (¬ p4112) ∨ (¬ p4391) ∨ (¬ p4717))
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ (¬ p4391) ∨ (¬ p3868) ∨ (¬ p3016) ∨ (¬ p3741) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4717 := h105424;
    let u6 : (¬ p4112) := (Or.elim h61630 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96077 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114010 (p2264 p2437 p2573 p2655 p2911 p3016 p4112 : Prop)
    (h99338 : (¬ p2911) ∨ (¬ p3016) ∨ p2573 ∨ p2264 ∨ (¬ p2655) ∨ (¬ p4112))
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ (¬ p2911) ∨ p2573 ∨ p2264 ∨ (¬ p3016) ∨ (¬ p2655) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4112) := (Or.elim h99338 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h96077 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114012 (p2417 p2437 p2449 p3016 p3741 p4112 p4717 : Prop)
    (h105424 : p4717)
    (h100124 : p2449 ∨ (¬ p2417) ∨ (¬ p4717) ∨ (¬ p3016) ∨ (¬ p4112) ∨ (¬ p3741))
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ (¬ p2417) ∨ p2449 ∨ (¬ p3016) ∨ (¬ p3741) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4717 := h105424;
    let u6 : (¬ p4112) := (Or.elim h100124 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h96077 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114014 (p2417 p2437 p2553 p3016 p3516 p4112 p4155 : Prop)
    (h109154 : p2553 ∨ (¬ p2417) ∨ (¬ p4155) ∨ p3516 ∨ (¬ p4112) ∨ (¬ p3016))
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ p2553 ∨ (¬ p2417) ∨ (¬ p4155) ∨ p3516 ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4112) := (Or.elim h109154 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96077 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114023 (p2264 p2341 p2437 p3016 p4109 p4112 p4717 p4988 : Prop)
    (h105424 : p4717)
    (h94478 : (¬ p2341) ∨ (¬ p4988) ∨ (¬ p4109) ∨ (¬ p4112) ∨ p2264 ∨ (¬ p3016) ∨ (¬ p4717))
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ (¬ p4988) ∨ (¬ p2341) ∨ p2264 ∨ (¬ p3016) ∨ (¬ p4109) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4717 := h105424;
    let u7 : (¬ p4112) := (Or.elim h94478 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u6))))))))))))));
    (Or.elim h96077 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114025 (p2264 p2341 p2437 p2737 p2811 p3016 p4104 p4112 : Prop)
    (h99449 : (¬ p2341) ∨ (¬ p2737) ∨ (¬ p4112) ∨ p2264 ∨ (¬ p3016) ∨ (¬ p2811) ∨ (¬ p4104))
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ p2264 ∨ (¬ p2341) ∨ (¬ p3016) ∨ (¬ p4104) ∨ (¬ p2811) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2264) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4112) := (Or.elim h99449 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u4))))))))))))));
    (Or.elim h96077 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114031 (p2220 p2437 p3016 p3146 p3266 p3399 p4075 p4112 p4391 : Prop)
    (h97254 : (¬ p4075) ∨ p3266 ∨ (¬ p3016) ∨ p2220 ∨ p3146 ∨ (¬ p4112) ∨ (¬ p3399) ∨ (¬ p4391))
    (h96077 : p4112 ∨ p2437)
    : p2437 ∨ p2220 ∨ p3146 ∨ (¬ p3016) ∨ (¬ p3399) ∨ p3266 ∨ (¬ p4075) ∨ (¬ p4391) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4112) := (Or.elim h97254 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h96077 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114034 (p2598 p2707 p2737 p3425 p4400 : Prop)
    (h113569 : p2707 ∨ (¬ p4400) ∨ p3425 ∨ (¬ p2737) ∨ p2598)
    (h96392 : p4400 ∨ p2707)
    : p2707 ∨ p3425 ∨ (¬ p2737) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2707) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3425) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4400) := (Or.elim h113569 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h96392 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114036 (p2707 p2737 p2774 p3425 p4400 p4842 : Prop)
    (h113568 : p2707 ∨ (¬ p4400) ∨ p3425 ∨ p2774 ∨ (¬ p2737) ∨ (¬ p4842))
    (h96392 : p4400 ∨ p2707)
    : p2707 ∨ p3425 ∨ p2774 ∨ (¬ p2737) ∨ (¬ p4842) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2707) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3425) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4400) := (Or.elim h113568 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h96392 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114038 (p2630 p3364 p4881 : Prop)
    (h67309 : p4881 ∨ (¬ p3364))
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ p4881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4881) := (fun h => hn (Or.inr h));
    let u2 : (¬ p3364) := (Or.elim h67309 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h88126 (fun q0 => (False.elim (u2 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114039 (p2630 p2737 p3364 p3367 : Prop)
    (h81274 : p2737 ∨ (¬ p3367) ∨ (¬ p3364))
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ p2737 ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3364) := (Or.elim h81274 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h88126 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114040 (p2598 p2630 p2737 p2753 p3364 : Prop)
    (h81283 : p2737 ∨ (¬ p2753) ∨ (¬ p2598) ∨ (¬ p3364))
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ (¬ p2598) ∨ (¬ p2753) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3364) := (Or.elim h81283 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => r2))))));
    (Or.elim h88126 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114041 (p2630 p2696 p3362 p3363 p3364 : Prop)
    (h82871 : p2696 ∨ (¬ p3364) ∨ (¬ p3363) ∨ (¬ p3362))
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ (¬ p3362) ∨ (¬ p3363) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3364) := (Or.elim h82871 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u1))))))));
    (Or.elim h88126 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114042 (p2437 p2630 p3136 p3201 p3364 : Prop)
    (h84388 : (¬ p3136) ∨ p3201 ∨ (¬ p2437) ∨ (¬ p3364))
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ (¬ p2437) ∨ p3201 ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3364) := (Or.elim h84388 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => r2))))));
    (Or.elim h88126 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114043 (p2630 p3083 p3136 p3364 p3641 : Prop)
    (h97302 : (¬ p3083) ∨ (¬ p3136) ∨ p3641 ∨ (¬ p3364))
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ p3641 ∨ (¬ p3083) ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3364) := (Or.elim h97302 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => r2))))));
    (Or.elim h88126 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114044 (p2630 p3136 p3343 p3364 p5160 : Prop)
    (h99797 : (¬ p3343) ∨ (¬ p5160) ∨ (¬ p3136) ∨ (¬ p3364))
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ (¬ p5160) ∨ (¬ p3343) ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3364) := (Or.elim h99797 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => r2))))));
    (Or.elim h88126 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114045 (p2437 p2630 p2911 p3016 p3364 p3422 : Prop)
    (h75118 : p2437 ∨ (¬ p3016) ∨ (¬ p3364) ∨ p2911 ∨ p3422)
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ p3422 ∨ p2437 ∨ (¬ p3016) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3364) := (Or.elim h75118 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h88126 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114046 (p2630 p2946 p3136 p3364 p3367 p4236 : Prop)
    (h84320 : (¬ p4236) ∨ (¬ p3367) ∨ (¬ p3136) ∨ (¬ p3364) ∨ p2946)
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ (¬ p3136) ∨ p2946 ∨ (¬ p3367) ∨ (¬ p4236) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3364) := (Or.elim h84320 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h88126 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114047 (p2630 p2946 p3016 p3136 p3364 p3422 : Prop)
    (h84321 : p2946 ∨ (¬ p3136) ∨ (¬ p3016) ∨ p3422 ∨ (¬ p3364))
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ (¬ p3016) ∨ (¬ p3136) ∨ p2946 ∨ p3422 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3364) := (Or.elim h84321 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => r3))))))));
    (Or.elim h88126 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114049 (p2437 p2630 p2651 p3201 p3364 p4790 : Prop)
    (h106424 : p4790)
    (h84432 : p3201 ∨ (¬ p2437) ∨ (¬ p3364) ∨ (¬ p4790) ∨ (¬ p2651))
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ p3201 ∨ (¬ p2437) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4790 := h106424;
    let u5 : (¬ p3364) := (Or.elim h84432 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h88126 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114050 (p2440 p2630 p2651 p2850 p3364 p4790 : Prop)
    (h106424 : p4790)
    (h84437 : (¬ p2651) ∨ p2440 ∨ (¬ p4790) ∨ p2850 ∨ (¬ p3364))
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ p2850 ∨ (¬ p2651) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4790 := h106424;
    let u5 : (¬ p3364) := (Or.elim h84437 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => r3))))))));
    (Or.elim h88126 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114052 (p2406 p2630 p2797 p2850 p3364 p3379 : Prop)
    (h91059 : (¬ p2406) ∨ (¬ p2797) ∨ p2850 ∨ (¬ p3364) ∨ (¬ p3379))
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ (¬ p2797) ∨ p2850 ∨ (¬ p3379) ∨ (¬ p2406) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3364) := (Or.elim h91059 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h88126 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114054 (p2518 p2630 p2839 p3364 p3541 p3641 : Prop)
    (h99679 : (¬ p2518) ∨ (¬ p3541) ∨ p2839 ∨ p3641 ∨ (¬ p3364))
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ (¬ p2518) ∨ p3641 ∨ p2839 ∨ (¬ p3541) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3364) := (Or.elim h99679 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => r3))))))));
    (Or.elim h88126 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114055 (p2132 p2573 p2630 p3362 p3364 p3422 : Prop)
    (h99726 : p2132 ∨ p3422 ∨ (¬ p2573) ∨ (¬ p3364) ∨ (¬ p3362))
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ (¬ p2573) ∨ p3422 ∨ p2132 ∨ (¬ p3362) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3364) := (Or.elim h99726 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h88126 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114056 (p2132 p2470 p2630 p3362 p3364 p3641 : Prop)
    (h99728 : p3641 ∨ (¬ p2470) ∨ p2132 ∨ (¬ p3362) ∨ (¬ p3364))
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ (¬ p2470) ∨ p3641 ∨ p2132 ∨ (¬ p3362) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3364) := (Or.elim h99728 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h88126 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114057 (p2132 p2630 p3355 p3362 p3364 p5160 : Prop)
    (h99796 : (¬ p5160) ∨ p2132 ∨ (¬ p3355) ∨ (¬ p3362) ∨ (¬ p3364))
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ (¬ p5160) ∨ (¬ p3355) ∨ (¬ p3362) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3364) := (Or.elim h99796 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => r3))))))));
    (Or.elim h88126 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114058 (p2630 p2727 p2751 p3343 p3364 p5160 : Prop)
    (h106343 : p2751)
    (h41675 : (¬ p2727) ∨ (¬ p2751) ∨ (¬ p3343) ∨ (¬ p3364) ∨ (¬ p5160))
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ (¬ p5160) ∨ (¬ p2727) ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2751 := h106343;
    let u5 : (¬ p3364) := (Or.elim h41675 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h88126 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114059 (p2630 p2651 p3016 p3364 p3422 p4790 : Prop)
    (h106424 : p4790)
    (h101257 : p3422 ∨ (¬ p3016) ∨ (¬ p3364) ∨ (¬ p4790) ∨ (¬ p2651))
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ p3422 ∨ (¬ p2651) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4790 := h106424;
    let u5 : (¬ p3364) := (Or.elim h101257 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h88126 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114062 (p2264 p2630 p2717 p2996 p3201 p3364 : Prop)
    (h111406 : p3201 ∨ (¬ p2264) ∨ p2996 ∨ p2717 ∨ (¬ p3364))
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ p3201 ∨ (¬ p2264) ∨ p2996 ∨ p2717 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3364) := (Or.elim h111406 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => r3))))))));
    (Or.elim h88126 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114063 (p2166 p2630 p2850 p3146 p3266 p3364 p4210 : Prop)
    (h76079 : (¬ p3364) ∨ p3146 ∨ (¬ p4210) ∨ p3266 ∨ p2850 ∨ p2166)
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ p3146 ∨ (¬ p4210) ∨ p2166 ∨ p2850 ∨ p3266 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3364) := (Or.elim h76079 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (u3 r4))))))))))));
    (Or.elim h88126 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114065 (p2518 p2630 p2651 p3364 p3641 p4116 p4790 : Prop)
    (h106424 : p4790)
    (h81499 : (¬ p2518) ∨ (¬ p4116) ∨ (¬ p3364) ∨ (¬ p4790) ∨ (¬ p2651) ∨ p3641)
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ (¬ p2518) ∨ p3641 ∨ (¬ p4116) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4790 := h106424;
    let u6 : (¬ p3364) := (Or.elim h81499 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (u2 r4))))))))))));
    (Or.elim h88126 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114066 (p2573 p2630 p2727 p2751 p3016 p3363 p3364 : Prop)
    (h106343 : p2751)
    (h82212 : (¬ p2751) ∨ p2573 ∨ (¬ p2727) ∨ (¬ p3363) ∨ (¬ p3364) ∨ (¬ p3016))
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ (¬ p3363) ∨ p2573 ∨ (¬ p2727) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2751 := h106343;
    let u6 : (¬ p3364) := (Or.elim h82212 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h88126 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114067 (p2230 p2630 p2656 p2727 p2751 p2850 p3364 : Prop)
    (h106343 : p2751)
    (h82298 : (¬ p3364) ∨ (¬ p2751) ∨ (¬ p2727) ∨ (¬ p2230) ∨ (¬ p2656) ∨ p2850)
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ p2850 ∨ (¬ p2230) ∨ (¬ p2656) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2751 := h106343;
    let u6 : (¬ p3364) := (Or.elim h82298 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u1 r4))))))))))));
    (Or.elim h88126 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114069 (p2406 p2630 p2707 p2850 p3364 p3541 p4778 : Prop)
    (h88295 : p2707 ∨ (¬ p3541) ∨ (¬ p3364) ∨ (¬ p2406) ∨ p2850 ∨ (¬ p4778))
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ p2707 ∨ (¬ p2406) ∨ (¬ p3541) ∨ p2850 ∨ (¬ p4778) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3364) := (Or.elim h88295 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h88126 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114071 (p2406 p2630 p2774 p2829 p2850 p3364 p3541 : Prop)
    (h90481 : p2829 ∨ (¬ p3364) ∨ (¬ p2406) ∨ (¬ p2774) ∨ (¬ p3541) ∨ p2850)
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ (¬ p3541) ∨ (¬ p2406) ∨ p2850 ∨ (¬ p2774) ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3364) := (Or.elim h90481 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (u3 r4))))))))))));
    (Or.elim h88126 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114073 (p2573 p2630 p2656 p2727 p2751 p3364 p3422 : Prop)
    (h106343 : p2751)
    (h101450 : p3422 ∨ (¬ p2573) ∨ (¬ p3364) ∨ (¬ p2751) ∨ (¬ p2656) ∨ (¬ p2727))
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ p3422 ∨ (¬ p2573) ∨ (¬ p2727) ∨ (¬ p2656) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2751 := h106343;
    let u6 : (¬ p3364) := (Or.elim h101450 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h88126 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114076 (p2230 p2630 p2656 p2797 p2850 p3364 p4975 : Prop)
    (h105464 : p4975)
    (h101831 : p2850 ∨ (¬ p3364) ∨ (¬ p2656) ∨ (¬ p4975) ∨ (¬ p2230) ∨ (¬ p2797))
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ (¬ p2797) ∨ p2850 ∨ (¬ p2230) ∨ (¬ p2656) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4975 := h105464;
    let u6 : (¬ p3364) := (Or.elim h101831 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h88126 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114077 (p2630 p2656 p2727 p2751 p3201 p3364 p3389 : Prop)
    (h106343 : p2751)
    (h101840 : p3201 ∨ (¬ p3389) ∨ (¬ p2656) ∨ (¬ p2751) ∨ (¬ p3364) ∨ (¬ p2727))
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ (¬ p3389) ∨ p3201 ∨ (¬ p2656) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2751 := h106343;
    let u6 : (¬ p3364) := (Or.elim h101840 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h88126 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114084 (p2573 p2630 p2751 p2951 p2992 p3364 p3422 p3904 : Prop)
    (h106343 : p2751)
    (h94560 : (¬ p2951) ∨ (¬ p2992) ∨ p3422 ∨ (¬ p3364) ∨ (¬ p2573) ∨ (¬ p3904) ∨ (¬ p2751))
    (h88126 : p3364 ∨ p2630)
    : p2630 ∨ (¬ p2951) ∨ p3422 ∨ (¬ p2573) ∨ (¬ p3904) ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2751 := h106343;
    let u7 : (¬ p3364) := (Or.elim h94560 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u6))))))))))))));
    (Or.elim h88126 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114104 (p2284 p2641 p2992 p4336 : Prop)
    (h81807 : p2641 ∨ (¬ p2992) ∨ (¬ p4336))
    (h79172 : p4336 ∨ (¬ p2284))
    : (¬ p2284) ∨ (¬ p2992) ∨ p2641 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4336) := (Or.elim h81807 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h79172 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114105 (p2284 p2797 p3136 p4336 : Prop)
    (h84339 : p2797 ∨ (¬ p3136) ∨ (¬ p4336))
    (h79172 : p4336 ∨ (¬ p2284))
    : (¬ p2284) ∨ (¬ p3136) ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4336) := (Or.elim h84339 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h79172 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114106 (p2284 p2331 p2946 p4336 : Prop)
    (h24463 : p2331 ∨ (¬ p2946) ∨ (¬ p4336))
    (h79172 : p4336 ∨ (¬ p2284))
    : (¬ p2284) ∨ p2331 ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4336) := (Or.elim h24463 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h79172 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114107 (p2284 p3019 p3413 p4336 : Prop)
    (h23675 : p3019 ∨ (¬ p3413) ∨ (¬ p4336))
    (h79172 : p4336 ∨ (¬ p2284))
    : (¬ p2284) ∨ p3019 ∨ (¬ p3413) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3019) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4336) := (Or.elim h23675 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h79172 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114109 (p2284 p2295 p2995 p4336 : Prop)
    (h113668 : (¬ p2295) ∨ p2995 ∨ (¬ p4336))
    (h79172 : p4336 ∨ (¬ p2284))
    : (¬ p2284) ∨ (¬ p2295) ∨ p2995 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2995) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4336) := (Or.elim h113668 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h79172 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114110 (p2284 p2295 p2901 p4275 p4336 : Prop)
    (h78210 : (¬ p2295) ∨ (¬ p4275) ∨ p2901 ∨ (¬ p4336))
    (h79172 : p4336 ∨ (¬ p2284))
    : (¬ p2284) ∨ (¬ p2295) ∨ p2901 ∨ (¬ p4275) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4336) := (Or.elim h78210 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => r2))))));
    (Or.elim h79172 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114111 (p2284 p2668 p3156 p4336 p4506 : Prop)
    (h26917 : (¬ p2668) ∨ p3156 ∨ (¬ p4336) ∨ (¬ p4506))
    (h79172 : p4336 ∨ (¬ p2284))
    : (¬ p2284) ∨ (¬ p2668) ∨ (¬ p4506) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4336) := (Or.elim h26917 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h79172 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114114 (p2187 p2274 p2284 p2295 p2946 p4336 : Prop)
    (h79409 : (¬ p2295) ∨ p2274 ∨ (¬ p2946) ∨ (¬ p4336) ∨ (¬ p2187))
    (h79172 : p4336 ∨ (¬ p2284))
    : (¬ p2284) ∨ p2274 ∨ (¬ p2187) ∨ (¬ p2295) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4336) := (Or.elim h79409 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h79172 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114115 (p2187 p2284 p2630 p2668 p3136 p4336 : Prop)
    (h84314 : (¬ p3136) ∨ (¬ p2668) ∨ p2187 ∨ p2630 ∨ (¬ p4336))
    (h79172 : p4336 ∨ (¬ p2284))
    : (¬ p2284) ∨ p2187 ∨ (¬ p2668) ∨ p2630 ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2187) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4336) := (Or.elim h84314 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => r3))))))));
    (Or.elim h79172 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114116 (p2187 p2284 p2668 p2727 p2992 p4336 : Prop)
    (h85882 : (¬ p2668) ∨ (¬ p2992) ∨ p2187 ∨ (¬ p4336) ∨ p2727)
    (h79172 : p4336 ∨ (¬ p2284))
    : (¬ p2284) ∨ (¬ p2992) ∨ p2727 ∨ (¬ p2668) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4336) := (Or.elim h85882 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h79172 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114117 (p2274 p2284 p2295 p2727 p2992 p4336 : Prop)
    (h85883 : p2727 ∨ (¬ p2992) ∨ p2274 ∨ (¬ p2295) ∨ (¬ p4336))
    (h79172 : p4336 ∨ (¬ p2284))
    : (¬ p2284) ∨ (¬ p2992) ∨ (¬ p2295) ∨ p2274 ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4336) := (Or.elim h85883 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h79172 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114118 (p2187 p2284 p2992 p3125 p3323 p4336 : Prop)
    (h85930 : (¬ p4336) ∨ (¬ p2187) ∨ (¬ p2992) ∨ (¬ p3323) ∨ p3125)
    (h79172 : p4336 ∨ (¬ p2284))
    : (¬ p2284) ∨ p3125 ∨ (¬ p3323) ∨ (¬ p2187) ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4336) := (Or.elim h85930 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h79172 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114121 (p2284 p2901 p3125 p3323 p4336 p4555 : Prop)
    (h105542 : p4555)
    (h98775 : (¬ p3323) ∨ p3125 ∨ (¬ p4336) ∨ p2901 ∨ (¬ p4555))
    (h79172 : p4336 ∨ (¬ p2284))
    : (¬ p2284) ∨ (¬ p3323) ∨ p3125 ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4555 := h105542;
    let u5 : (¬ p4336) := (Or.elim h98775 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h79172 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114125 (p2187 p2274 p2284 p2307 p3136 p3567 p4336 : Prop)
    (h78392 : p2274 ∨ (¬ p2187) ∨ (¬ p2307) ∨ (¬ p3567) ∨ (¬ p4336) ∨ (¬ p3136))
    (h79172 : p4336 ∨ (¬ p2284))
    : (¬ p2284) ∨ p2274 ∨ (¬ p2307) ∨ (¬ p3567) ∨ (¬ p3136) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4336) := (Or.elim h78392 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h79172 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114127 (p2284 p2295 p2307 p2785 p3156 p4185 p4336 : Prop)
    (h79086 : (¬ p2295) ∨ p2307 ∨ (¬ p4185) ∨ (¬ p4336) ∨ (¬ p2785) ∨ p3156)
    (h79172 : p4336 ∨ (¬ p2284))
    : (¬ p2284) ∨ (¬ p2785) ∨ p3156 ∨ (¬ p2295) ∨ p2307 ∨ (¬ p4185) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4336) := (Or.elim h79086 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (u2 r4))))))))))));
    (Or.elim h79172 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114128 (p2284 p2383 p2563 p2668 p4336 p4356 p4705 : Prop)
    (h106238 : p4705)
    (h79236 : (¬ p2668) ∨ (¬ p4336) ∨ p2383 ∨ (¬ p4705) ∨ p2563 ∨ (¬ p4356))
    (h79172 : p4336 ∨ (¬ p2284))
    : (¬ p2284) ∨ p2563 ∨ (¬ p2668) ∨ (¬ p4356) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4705 := h106238;
    let u6 : (¬ p4336) := (Or.elim h79236 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h79172 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114132 (p2284 p2295 p2307 p2860 p4336 p4356 p4906 : Prop)
    (h105632 : p4906)
    (h79412 : (¬ p2295) ∨ p2307 ∨ (¬ p4356) ∨ (¬ p4336) ∨ p2860 ∨ (¬ p4906))
    (h79172 : p4336 ∨ (¬ p2284))
    : (¬ p2284) ∨ p2860 ∨ (¬ p2295) ∨ p2307 ∨ (¬ p4356) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2860) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4906 := h105632;
    let u6 : (¬ p4336) := (Or.elim h79412 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h79172 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114133 (p2284 p2295 p2307 p2563 p4336 p4356 p4705 : Prop)
    (h106238 : p4705)
    (h79414 : (¬ p2295) ∨ p2307 ∨ p2563 ∨ (¬ p4705) ∨ (¬ p4356) ∨ (¬ p4336))
    (h79172 : p4336 ∨ (¬ p2284))
    : (¬ p2284) ∨ (¬ p2295) ∨ (¬ p4356) ∨ p2307 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4705 := h106238;
    let u6 : (¬ p4336) := (Or.elim h79414 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => r4))))))))));
    (Or.elim h79172 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114134 (p2284 p2383 p2668 p2860 p4336 p4356 p4906 : Prop)
    (h105632 : p4906)
    (h83306 : (¬ p4336) ∨ (¬ p2668) ∨ (¬ p4356) ∨ p2383 ∨ p2860 ∨ (¬ p4906))
    (h79172 : p4336 ∨ (¬ p2284))
    : (¬ p2284) ∨ p2860 ∨ (¬ p2668) ∨ p2383 ∨ (¬ p4356) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2860) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4906 := h105632;
    let u6 : (¬ p4336) := (Or.elim h83306 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h79172 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114137 (p2274 p2284 p2307 p2630 p3136 p3567 p4336 : Prop)
    (h84312 : (¬ p3136) ∨ (¬ p2307) ∨ p2274 ∨ p2630 ∨ (¬ p3567) ∨ (¬ p4336))
    (h79172 : p4336 ∨ (¬ p2284))
    : (¬ p2284) ∨ p2274 ∨ (¬ p2307) ∨ (¬ p3136) ∨ p2630 ∨ (¬ p3567) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4336) := (Or.elim h84312 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h79172 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114138 (p2156 p2284 p3125 p3323 p3645 p4336 p4957 : Prop)
    (h85495 : (¬ p4336) ∨ (¬ p3323) ∨ (¬ p4957) ∨ p2156 ∨ p3125 ∨ (¬ p3645))
    (h79172 : p4336 ∨ (¬ p2284))
    : (¬ p2284) ∨ p3125 ∨ (¬ p3323) ∨ (¬ p4957) ∨ p2156 ∨ (¬ p3645) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4336) := (Or.elim h85495 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h79172 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114140 (p2284 p2563 p3323 p3654 p4336 p4356 p4705 : Prop)
    (h106238 : p4705)
    (h90905 : (¬ p3323) ∨ p3654 ∨ (¬ p4705) ∨ (¬ p4356) ∨ (¬ p4336) ∨ p2563)
    (h79172 : p4336 ∨ (¬ p2284))
    : (¬ p2284) ∨ p2563 ∨ p3654 ∨ (¬ p4356) ∨ (¬ p3323) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4705 := h106238;
    let u6 : (¬ p4336) := (Or.elim h90905 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (u1 r4))))))))))));
    (Or.elim h79172 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114141 (p2192 p2284 p3156 p3747 p4228 p4336 p4393 : Prop)
    (h96109 : (¬ p4228) ∨ (¬ p4393) ∨ (¬ p3747) ∨ p2192 ∨ p3156 ∨ (¬ p4336))
    (h79172 : p4336 ∨ (¬ p2284))
    : (¬ p2284) ∨ (¬ p4228) ∨ (¬ p4393) ∨ p2192 ∨ (¬ p3747) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4228 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4336) := (Or.elim h96109 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => r4))))))))));
    (Or.elim h79172 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114142 (p2156 p2284 p3156 p3747 p4228 p4336 p4393 : Prop)
    (h96116 : (¬ p4228) ∨ (¬ p4393) ∨ p2156 ∨ p3156 ∨ (¬ p4336) ∨ (¬ p3747))
    (h79172 : p4336 ∨ (¬ p2284))
    : (¬ p2284) ∨ (¬ p4228) ∨ (¬ p4393) ∨ p2156 ∨ (¬ p3747) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4228 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4336) := (Or.elim h96116 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h79172 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114154 (p2284 p2341 p2662 p2717 p2797 p4336 p4781 p5197 : Prop)
    (h94440 : p2797 ∨ (¬ p2717) ∨ (¬ p2662) ∨ (¬ p4781) ∨ p2341 ∨ (¬ p4336) ∨ (¬ p5197))
    (h79172 : p4336 ∨ (¬ p2284))
    : (¬ p2284) ∨ (¬ p4781) ∨ p2797 ∨ (¬ p2717) ∨ p2341 ∨ (¬ p2662) ∨ (¬ p5197) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4336) := (Or.elim h94440 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (r5 u6))))))))))))));
    (Or.elim h79172 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114170 (p2417 p2459 p2911 p3945 : Prop)
    (h6932 : p2417 ∨ (¬ p2911) ∨ (¬ p3945))
    (h92417 : p3945 ∨ (¬ p2459))
    : (¬ p2459) ∨ (¬ p2911) ∨ p2417 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3945) := (Or.elim h6932 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h92417 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114171 (p2177 p2396 p2459 p3945 : Prop)
    (h15523 : (¬ p2177) ∨ p2396 ∨ (¬ p3945))
    (h92417 : p3945 ∨ (¬ p2459))
    : (¬ p2459) ∨ p2396 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3945) := (Or.elim h15523 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h92417 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114172 (p2459 p2881 p3246 p3945 : Prop)
    (h23854 : (¬ p2881) ∨ p3246 ∨ (¬ p3945))
    (h92417 : p3945 ∨ (¬ p2459))
    : (¬ p2459) ∨ p3246 ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3945) := (Or.elim h23854 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h92417 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114173 (p2264 p2449 p2459 p3945 : Prop)
    (h100136 : p2449 ∨ (¬ p2264) ∨ (¬ p3945))
    (h92417 : p3945 ∨ (¬ p2459))
    : (¬ p2459) ∨ p2449 ∨ (¬ p2264) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3945) := (Or.elim h100136 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h92417 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114174 (p2459 p3527 p3631 p3945 : Prop)
    (h101977 : p3631 ∨ (¬ p3527) ∨ (¬ p3945))
    (h92417 : p3945 ∨ (¬ p2459))
    : (¬ p2459) ∨ (¬ p3527) ∨ p3631 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3945) := (Or.elim h101977 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h92417 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114175 (p2459 p2717 p3434 p3945 : Prop)
    (h102152 : p3434 ∨ (¬ p2717) ∨ (¬ p3945))
    (h92417 : p3945 ∨ (¬ p2459))
    : (¬ p2459) ∨ (¬ p2717) ∨ p3434 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3945) := (Or.elim h102152 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h92417 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114176 (p2341 p2459 p3516 p3945 : Prop)
    (h110099 : p3516 ∨ (¬ p3945) ∨ (¬ p2341))
    (h92417 : p3945 ∨ (¬ p2459))
    : (¬ p2459) ∨ p3516 ∨ (¬ p2341) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3516) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3945) := (Or.elim h110099 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h92417 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114180 (p2459 p2707 p3434 p3527 p3945 : Prop)
    (h113557 : p2707 ∨ (¬ p3527) ∨ p3434 ∨ (¬ p3945))
    (h92417 : p3945 ∨ (¬ p2459))
    : (¬ p2459) ∨ p2707 ∨ (¬ p3527) ∨ p3434 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3945) := (Or.elim h113557 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => r2))))));
    (Or.elim h92417 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114181 (p2459 p2528 p2761 p3266 p3945 p4420 : Prop)
    (h105707 : p4420)
    (h79580 : p3266 ∨ (¬ p2761) ∨ (¬ p3945) ∨ (¬ p4420) ∨ p2528)
    (h92417 : p3945 ∨ (¬ p2459))
    : (¬ p2459) ∨ (¬ p2761) ∨ p2528 ∨ p3266 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4420 := h105707;
    let u5 : (¬ p3945) := (Or.elim h79580 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h92417 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114182 (p2363 p2459 p2761 p3266 p3945 p4133 : Prop)
    (h105712 : p4133)
    (h79611 : p3266 ∨ (¬ p2761) ∨ p2363 ∨ (¬ p3945) ∨ (¬ p4133))
    (h92417 : p3945 ∨ (¬ p2459))
    : (¬ p2459) ∨ p2363 ∨ (¬ p2761) ∨ p3266 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4133 := h105712;
    let u5 : (¬ p3945) := (Or.elim h79611 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h92417 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114185 (p2459 p2761 p3146 p3266 p3945 p4902 : Prop)
    (h105456 : p4902)
    (h98674 : p3266 ∨ (¬ p2761) ∨ p3146 ∨ (¬ p3945) ∨ (¬ p4902))
    (h92417 : p3945 ∨ (¬ p2459))
    : (¬ p2459) ∨ p3146 ∨ (¬ p2761) ∨ p3266 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4902 := h105456;
    let u5 : (¬ p3945) := (Or.elim h98674 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h92417 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114188 (p2177 p2449 p2459 p2641 p2996 p3945 : Prop)
    (h99943 : (¬ p2641) ∨ p2449 ∨ (¬ p2996) ∨ (¬ p2177) ∨ (¬ p3945))
    (h92417 : p3945 ∨ (¬ p2459))
    : (¬ p2459) ∨ (¬ p2996) ∨ (¬ p2641) ∨ p2449 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3945) := (Or.elim h99943 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h92417 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114193 (p2459 p3063 p3093 p3631 p3830 p3945 : Prop)
    (h110533 : p3631 ∨ (¬ p3063) ∨ p3830 ∨ (¬ p3945) ∨ (¬ p3093))
    (h92417 : p3945 ∨ (¬ p2459))
    : (¬ p2459) ∨ p3631 ∨ (¬ p3063) ∨ p3830 ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3631) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3945) := (Or.elim h110533 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h92417 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114194 (p2177 p2449 p2459 p2761 p3945 p5284 : Prop)
    (h110905 : p2449 ∨ (¬ p3945) ∨ (¬ p5284) ∨ (¬ p2177) ∨ (¬ p2761))
    (h92417 : p3945 ∨ (¬ p2459))
    : (¬ p2459) ∨ p2449 ∨ (¬ p5284) ∨ (¬ p2177) ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3945) := (Or.elim h110905 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h92417 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114199 (p2459 p3146 p3266 p3276 p3945 p4636 p4902 : Prop)
    (h105456 : p4902)
    (h79572 : (¬ p3276) ∨ p3266 ∨ (¬ p4636) ∨ p3146 ∨ (¬ p3945) ∨ (¬ p4902))
    (h92417 : p3945 ∨ (¬ p2459))
    : (¬ p2459) ∨ (¬ p3276) ∨ p3266 ∨ (¬ p4636) ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4636 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4902 := h105456;
    let u6 : (¬ p3945) := (Or.elim h79572 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h92417 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114213 (p2264 p2396 p2459 p2553 p2573 p3073 p3256 p3449 p3945 : Prop)
    (h112930 : p2264 ∨ p2553 ∨ (¬ p3073) ∨ p2573 ∨ p3256 ∨ (¬ p3449) ∨ p2396 ∨ (¬ p3945))
    (h92417 : p3945 ∨ (¬ p2459))
    : (¬ p2459) ∨ p2264 ∨ p2553 ∨ (¬ p3073) ∨ p2573 ∨ p3256 ∨ (¬ p3449) ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2264) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p3945) := (Or.elim h112930 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => r6))))))))))))));
    (Or.elim h92417 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114227 (p2341 p2459 p2608 p2829 p2860 p3105 p3266 p3276 p3945 p4636 p5059 : Prop)
    (h113547 : (¬ p2860) ∨ (¬ p3276) ∨ (¬ p3945) ∨ p3266 ∨ p2829 ∨ (¬ p2341) ∨ p3105 ∨ p2608 ∨ (¬ p4636) ∨ (¬ p5059))
    (h92417 : p3945 ∨ (¬ p2459))
    : (¬ p2459) ∨ (¬ p2860) ∨ (¬ p3276) ∨ p3266 ∨ p2829 ∨ (¬ p2341) ∨ p3105 ∨ p2608 ∨ (¬ p4636) ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3105) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4636 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p3945) := (Or.elim h113547 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h92417 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114228 (p2363 p2449 p2459 p2663 p2774 p2807 p3363 p3367 p3609 p3945 p4133 p4861 : Prop)
    (h105712 : p4133)
    (h74994 : p2363 ∨ (¬ p4861) ∨ (¬ p3609) ∨ p2807 ∨ (¬ p3363) ∨ (¬ p2663) ∨ (¬ p2774) ∨ p2449 ∨ (¬ p4133) ∨ (¬ p3945) ∨ p3367)
    (h92417 : p3945 ∨ (¬ p2459))
    : (¬ p2459) ∨ (¬ p3609) ∨ (¬ p2774) ∨ p3367 ∨ p2807 ∨ p2363 ∨ p2449 ∨ (¬ p2663) ∨ (¬ p3363) ∨ (¬ p4861) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4861 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4133 := h105712;
    let u11 : (¬ p3945) := (Or.elim h74994 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => q9) (fun r9 => (False.elim (u3 r9))))))))))))))))))))));
    (Or.elim h92417 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114232 (p2264 p2331 p2427 p2459 p2797 p2982 p3005 p3051 p3246 p3904 p3945 p4117 : Prop)
    (h112960 : p2264 ∨ p3246 ∨ (¬ p3005) ∨ (¬ p3945) ∨ (¬ p2331) ∨ p2797 ∨ p2982 ∨ p3051 ∨ (¬ p4117) ∨ (¬ p3904) ∨ (¬ p2427))
    (h92417 : p3945 ∨ (¬ p2459))
    : (¬ p2459) ∨ p2264 ∨ p3246 ∨ (¬ p3005) ∨ (¬ p2331) ∨ p2797 ∨ p2982 ∨ p3051 ∨ (¬ p4117) ∨ (¬ p3904) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2264) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p3945) := (Or.elim h112960 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (False.elim (r9 u10))))))))))))))))))))));
    (Or.elim h92417 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114233 (p2396 p2459 p2553 p2573 p2753 p2946 p3005 p3136 p3347 p3945 p4117 p4311 p4902 : Prop)
    (h105456 : p4902)
    (h100781 : (¬ p3005) ∨ (¬ p2753) ∨ (¬ p3347) ∨ p2573 ∨ (¬ p4311) ∨ (¬ p4117) ∨ (¬ p3945) ∨ p3136 ∨ (¬ p2946) ∨ p2553 ∨ p2396 ∨ (¬ p4902))
    (h92417 : p3945 ∨ (¬ p2459))
    : (¬ p2459) ∨ (¬ p4311) ∨ p2396 ∨ p2553 ∨ p2573 ∨ p3136 ∨ (¬ p3005) ∨ (¬ p2753) ∨ (¬ p4117) ∨ (¬ p3347) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4902 := h105456;
    let u12 : (¬ p3945) := (Or.elim h100781 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u5 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u3 q9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (u2 q10))) (fun r10 => (False.elim (r10 u11))))))))))))))))))))))));
    (Or.elim h92417 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114238 (p2417 p2922 p2933 p3631 : Prop)
    (h95529 : (¬ p2417) ∨ p3631 ∨ (¬ p2933))
    (h96902 : p2933 ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p2417) ∨ p3631 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2933) := (Or.elim h95529 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h96902 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114239 (p2911 p2922 p2933 p3527 : Prop)
    (h95532 : (¬ p2933) ∨ p3527 ∨ (¬ p2911))
    (h96902 : p2933 ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p2911) ∨ p3527 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2933) := (Or.elim h95532 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h96902 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114240 (p2922 p2933 p3547 p4710 : Prop)
    (h32859 : (¬ p2933) ∨ p3547 ∨ (¬ p4710))
    (h96902 : p2933 ∨ (¬ p2922))
    : (¬ p2922) ∨ p3547 ∨ (¬ p4710) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3547) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2933) := (Or.elim h32859 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96902 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114241 (p2922 p2933 p3569 p3571 : Prop)
    (h5198 : (¬ p2933) ∨ (¬ p3569) ∨ p3571)
    (h96902 : p2933 ∨ (¬ p2922))
    : (¬ p2922) ∨ p3571 ∨ (¬ p3569) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3571) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2933) := (Or.elim h5198 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h96902 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114245 (p2881 p2922 p2933 p3527 p3569 : Prop)
    (h95544 : (¬ p2933) ∨ p3527 ∨ (¬ p3569) ∨ (¬ p2881))
    (h96902 : p2933 ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p2881) ∨ p3527 ∨ (¬ p3569) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2933) := (Or.elim h95544 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u1))))))));
    (Or.elim h96902 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114247 (p2717 p2922 p2933 p3389 p3527 p5085 : Prop)
    (h76885 : (¬ p2933) ∨ (¬ p2717) ∨ (¬ p5085) ∨ p3389 ∨ p3527)
    (h96902 : p2933 ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p2717) ∨ p3389 ∨ (¬ p5085) ∨ p3527 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5085 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2933) := (Or.elim h76885 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h96902 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114250 (p2230 p2870 p2922 p2933 p3389 p4909 : Prop)
    (h107326 : (¬ p2933) ∨ p3389 ∨ (¬ p2230) ∨ (¬ p4909) ∨ (¬ p2870))
    (h96902 : p2933 ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p4909) ∨ (¬ p2230) ∨ p3389 ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4909 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2933) := (Or.elim h107326 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96902 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114251 (p2437 p2922 p2933 p3379 p3399 p4814 : Prop)
    (h105440 : p4814)
    (h95506 : (¬ p3399) ∨ p3379 ∨ p2437 ∨ (¬ p2933) ∨ (¬ p4814))
    (h96902 : p2933 ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p3399) ∨ p2437 ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4814 := h105440;
    let u5 : (¬ p2933) := (Or.elim h95506 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96902 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114252 (p2417 p2761 p2922 p2933 p3379 p3399 : Prop)
    (h95508 : (¬ p3399) ∨ (¬ p2761) ∨ (¬ p2933) ∨ (¬ p2417) ∨ p3379)
    (h96902 : p2933 ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p2761) ∨ (¬ p2417) ∨ p3379 ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2933) := (Or.elim h95508 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h96902 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114254 (p2459 p2911 p2922 p2933 p3379 p3399 : Prop)
    (h95512 : (¬ p3399) ∨ p3379 ∨ (¬ p2459) ∨ (¬ p2933) ∨ (¬ p2911))
    (h96902 : p2933 ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p3399) ∨ p3379 ∨ (¬ p2911) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2933) := (Or.elim h95512 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h96902 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114255 (p2922 p2933 p3201 p3379 p3399 p5217 : Prop)
    (h105493 : p5217)
    (h95514 : (¬ p3399) ∨ p3379 ∨ p3201 ∨ (¬ p2933) ∨ (¬ p5217))
    (h96902 : p2933 ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p3399) ∨ p3201 ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5217 := h105493;
    let u5 : (¬ p2933) := (Or.elim h95514 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96902 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114258 (p2230 p2881 p2922 p2933 p3389 p3527 : Prop)
    (h99995 : (¬ p2933) ∨ p3527 ∨ (¬ p2230) ∨ (¬ p2881) ∨ p3389)
    (h96902 : p2933 ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p2881) ∨ p3527 ∨ p3389 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2933) := (Or.elim h99995 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h96902 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114260 (p2881 p2922 p2933 p3527 p3941 p5693 : Prop)
    (h112243 : p3527 ∨ (¬ p5693) ∨ (¬ p2881) ∨ (¬ p2933) ∨ (¬ p3941))
    (h96902 : p2933 ∨ (¬ p2922))
    : (¬ p2922) ∨ p3527 ∨ (¬ p5693) ∨ (¬ p2881) ∨ (¬ p3941) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3527) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2933) := (Or.elim h112243 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96902 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114268 (p2441 p2563 p2922 p2933 p3246 p3631 p4555 : Prop)
    (h105542 : p4555)
    (h95541 : p3631 ∨ (¬ p3246) ∨ (¬ p2933) ∨ (¬ p4555) ∨ (¬ p2563) ∨ (¬ p2441))
    (h96902 : p2933 ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p2441) ∨ (¬ p3246) ∨ (¬ p2563) ∨ p3631 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4555 := h105542;
    let u6 : (¬ p2933) := (Or.elim h95541 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h96902 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114271 (p2122 p2922 p2933 p3389 p3434 p3631 p4375 : Prop)
    (h111337 : (¬ p2122) ∨ p3631 ∨ p3389 ∨ (¬ p2933) ∨ (¬ p4375) ∨ (¬ p3434))
    (h96902 : p2933 ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p2122) ∨ p3631 ∨ p3389 ∨ (¬ p4375) ∨ (¬ p3434) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2933) := (Or.elim h111337 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96902 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114281 (p2440 p2668 p2922 p2933 p3019 p3073 p3256 p3527 : Prop)
    (h112841 : (¬ p2668) ∨ p3527 ∨ p3073 ∨ (¬ p3256) ∨ (¬ p2440) ∨ (¬ p3019) ∨ (¬ p2933))
    (h96902 : p2933 ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p2668) ∨ p3527 ∨ p3073 ∨ (¬ p3256) ∨ (¬ p2440) ∨ (¬ p3019) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2933) := (Or.elim h112841 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => r5))))))))))));
    (Or.elim h96902 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114287 (p2132 p2922 p2933 p3105 p3366 p3379 p3399 p3868 p4322 p4376 p4826 : Prop)
    (h106320 : p4376)
    (h105444 : p4826)
    (h84505 : (¬ p3868) ∨ (¬ p4322) ∨ (¬ p2933) ∨ p3105 ∨ (¬ p3366) ∨ (¬ p4826) ∨ p2132 ∨ (¬ p4376) ∨ (¬ p3399) ∨ p3379)
    (h96902 : p2933 ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p4322) ∨ (¬ p3399) ∨ p3379 ∨ p2132 ∨ p3105 ∨ (¬ p3366) ∨ (¬ p3868) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3105) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4376 := h106320;
    let u9 : p4826 := h105444;
    let u10 : (¬ p2933) := (Or.elim h84505 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (u3 r8))))))))))))))))))));
    (Or.elim h96902 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114288 (p2132 p2417 p2619 p2922 p2933 p3146 p3366 p3379 p3399 p3950 p4376 : Prop)
    (h106320 : p4376)
    (h84743 : p3146 ∨ (¬ p2417) ∨ p2132 ∨ (¬ p4376) ∨ p2619 ∨ (¬ p3950) ∨ (¬ p2933) ∨ (¬ p3399) ∨ p3379 ∨ (¬ p3366))
    (h96902 : p2933 ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p2417) ∨ p2619 ∨ p3146 ∨ (¬ p3399) ∨ p3379 ∨ p2132 ∨ (¬ p3366) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    let u10 : (¬ p2933) := (Or.elim h84743 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u5 q8))) (fun r8 => (False.elim (r8 u7))))))))))))))))))));
    (Or.elim h96902 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114289 (p2417 p2696 p2922 p2933 p3005 p3256 p3366 p3379 p3399 p3950 p4376 : Prop)
    (h106320 : p4376)
    (h95507 : (¬ p3399) ∨ p3005 ∨ (¬ p4376) ∨ (¬ p3950) ∨ (¬ p2417) ∨ p3256 ∨ p3379 ∨ (¬ p3366) ∨ (¬ p2933) ∨ p2696)
    (h96902 : p2933 ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p2417) ∨ p3256 ∨ (¬ p3399) ∨ (¬ p3950) ∨ p2696 ∨ p3005 ∨ (¬ p3366) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4376 := h106320;
    let u10 : (¬ p2933) := (Or.elim h95507 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u8 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => q8) (fun r8 => (False.elim (u5 r8))))))))))))))))))));
    (Or.elim h96902 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114292 (p2122 p2396 p2774 p2911 p2922 p2933 p3366 p3379 p3399 p4376 p4666 : Prop)
    (h105658 : p4666)
    (h106320 : p4376)
    (h97894 : (¬ p2933) ∨ p2396 ∨ p2774 ∨ (¬ p4376) ∨ p3379 ∨ (¬ p3366) ∨ (¬ p3399) ∨ p2122 ∨ (¬ p2911) ∨ (¬ p4666))
    (h96902 : p2933 ∨ (¬ p2922))
    : (¬ p2922) ∨ p2122 ∨ p2396 ∨ (¬ p2911) ∨ (¬ p3399) ∨ p2774 ∨ (¬ p3366) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4666 := h105658;
    let u9 : p4376 := h106320;
    let u10 : (¬ p2933) := (Or.elim h97894 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u8))))))))))))))))))));
    (Or.elim h96902 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114294 (p2136 p2241 p2417 p2922 p2933 p3105 p3366 p3399 p3461 p3670 p4032 : Prop)
    (h109442 : (¬ p3105) ∨ p3670 ∨ (¬ p2933) ∨ (¬ p2417) ∨ (¬ p3461) ∨ (¬ p3366) ∨ (¬ p4032) ∨ p2241 ∨ (¬ p3399) ∨ (¬ p2136))
    (h96902 : p2933 ∨ (¬ p2922))
    : (¬ p2922) ∨ (¬ p3105) ∨ p3670 ∨ (¬ p2417) ∨ (¬ p3461) ∨ (¬ p3366) ∨ (¬ p4032) ∨ p2241 ∨ (¬ p3399) ∨ (¬ p2136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3670) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2933) := (Or.elim h109442 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h96902 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114302 (p2437 p3016 p3740 p3920 : Prop)
    (h113975 : p2437 ∨ (¬ p3016) ∨ (¬ p3920) ∨ (¬ p3740))
    (h96076 : p3740 ∨ p2437)
    : p2437 ∨ (¬ p3016) ∨ (¬ p3920) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3920 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3740) := (Or.elim h113975 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => r2))))));
    (Or.elim h96076 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114304 (p2437 p3699 p3740 p4001 : Prop)
    (h34280 : p3699 ∨ (¬ p3740) ∨ (¬ p4001))
    (h96076 : p3740 ∨ p2437)
    : p2437 ∨ p3699 ∨ (¬ p4001) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3699) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3740) := (Or.elim h34280 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96076 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114305 (p2264 p2437 p2911 p3740 : Prop)
    (h76191 : p2911 ∨ (¬ p2264) ∨ (¬ p3740))
    (h96076 : p3740 ∨ p2437)
    : p2437 ∨ p2911 ∨ (¬ p2264) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2911) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3740) := (Or.elim h76191 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h96076 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114306 (p2417 p2437 p2449 p3740 : Prop)
    (h82164 : (¬ p2449) ∨ p2417 ∨ (¬ p3740))
    (h96076 : p3740 ∨ p2437)
    : p2437 ∨ (¬ p2449) ∨ p2417 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3740) := (Or.elim h82164 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h96076 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114307 (p2298 p2437 p3740 p3921 : Prop)
    (h25743 : p2298 ∨ (¬ p3740) ∨ (¬ p3921))
    (h96076 : p3740 ∨ p2437)
    : p2437 ∨ (¬ p3921) ∨ p2298 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2298) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3740) := (Or.elim h25743 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h96076 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114308 (p2437 p3575 p3740 p4066 : Prop)
    (h23380 : p3575 ∨ (¬ p3740) ∨ (¬ p4066))
    (h96076 : p3740 ∨ p2437)
    : p2437 ∨ p3575 ∨ (¬ p4066) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3575) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3740) := (Or.elim h23380 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96076 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114317 (p2437 p2727 p2996 p3201 p3740 p4753 : Prop)
    (h105514 : p4753)
    (h41264 : (¬ p2727) ∨ (¬ p2996) ∨ (¬ p3201) ∨ (¬ p3740) ∨ (¬ p4753))
    (h96076 : p3740 ∨ p2437)
    : p2437 ∨ (¬ p2996) ∨ (¬ p2727) ∨ (¬ p3201) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4753 := h105514;
    let u5 : (¬ p3740) := (Or.elim h41264 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96076 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114318 (p2241 p2437 p2608 p2911 p2996 p3740 : Prop)
    (h80782 : (¬ p2996) ∨ p2241 ∨ p2911 ∨ (¬ p3740) ∨ (¬ p2608))
    (h96076 : p3740 ∨ p2437)
    : p2437 ∨ (¬ p2996) ∨ (¬ p2608) ∨ p2241 ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3740) := (Or.elim h80782 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h96076 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114319 (p2437 p2665 p2727 p2996 p3389 p3740 : Prop)
    (h105373 : p2665)
    (h48358 : (¬ p2665) ∨ (¬ p2727) ∨ (¬ p2996) ∨ (¬ p3389) ∨ (¬ p3740))
    (h96076 : p3740 ∨ p2437)
    : p2437 ∨ (¬ p2996) ∨ (¬ p3389) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2665 := h105373;
    let u5 : (¬ p3740) := (Or.elim h48358 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h96076 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114324 (p2437 p2630 p2651 p2807 p2911 p3740 : Prop)
    (h99184 : (¬ p2651) ∨ (¬ p3740) ∨ p2807 ∨ p2630 ∨ p2911)
    (h96076 : p3740 ∨ p2437)
    : p2437 ∨ p2807 ∨ p2911 ∨ p2630 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2807) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3740) := (Or.elim h99184 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h96076 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114325 (p2437 p2651 p2727 p2807 p2911 p3740 : Prop)
    (h99187 : (¬ p2651) ∨ p2727 ∨ (¬ p3740) ∨ p2807 ∨ p2911)
    (h96076 : p3740 ∨ p2437)
    : p2437 ∨ p2911 ∨ p2727 ∨ p2807 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2911) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3740) := (Or.elim h99187 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h96076 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114326 (p2437 p2553 p2630 p2685 p3016 p3740 : Prop)
    (h109152 : p2553 ∨ p2685 ∨ (¬ p2630) ∨ (¬ p3740) ∨ (¬ p3016))
    (h96076 : p3740 ∨ p2437)
    : p2437 ∨ p2553 ∨ p2685 ∨ (¬ p2630) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3740) := (Or.elim h109152 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96076 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114327 (p2396 p2437 p2449 p2807 p3286 p3740 : Prop)
    (h110665 : (¬ p2449) ∨ (¬ p3740) ∨ p2396 ∨ p2807 ∨ (¬ p3286))
    (h96076 : p3740 ∨ p2437)
    : p2437 ∨ (¬ p2449) ∨ p2396 ∨ p2807 ∨ (¬ p3286) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3740) := (Or.elim h110665 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96076 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114329 (p2274 p2331 p2437 p2807 p3740 p3921 p4564 : Prop)
    (h105401 : p4564)
    (h75829 : (¬ p3921) ∨ (¬ p2331) ∨ p2807 ∨ (¬ p3740) ∨ (¬ p4564) ∨ (¬ p2274))
    (h96076 : p3740 ∨ p2437)
    : p2437 ∨ (¬ p3921) ∨ p2807 ∨ (¬ p2331) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4564 := h105401;
    let u6 : (¬ p3740) := (Or.elim h75829 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h96076 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114330 (p2264 p2406 p2437 p2881 p3389 p3519 p3740 : Prop)
    (h75830 : (¬ p2264) ∨ p2881 ∨ p2406 ∨ (¬ p3519) ∨ (¬ p3389) ∨ (¬ p3740))
    (h96076 : p3740 ∨ p2437)
    : p2437 ∨ p2881 ∨ (¬ p2264) ∨ (¬ p3519) ∨ (¬ p3389) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3740) := (Or.elim h75830 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h96076 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114332 (p2230 p2437 p2656 p2727 p2996 p3740 p4644 : Prop)
    (h105411 : p4644)
    (h49913 : (¬ p2230) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2996) ∨ (¬ p3740) ∨ (¬ p4644))
    (h96076 : p3740 ∨ p2437)
    : p2437 ∨ (¬ p2996) ∨ (¬ p2656) ∨ (¬ p2230) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4644 := h105411;
    let u6 : (¬ p3740) := (Or.elim h49913 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96076 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114335 (p2230 p2437 p2630 p2656 p2685 p3740 p4644 : Prop)
    (h105411 : p4644)
    (h87076 : p2685 ∨ (¬ p2656) ∨ (¬ p2630) ∨ (¬ p4644) ∨ (¬ p3740) ∨ (¬ p2230))
    (h96076 : p3740 ∨ p2437)
    : p2437 ∨ p2685 ∨ (¬ p2630) ∨ (¬ p2230) ∨ (¬ p2656) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4644 := h105411;
    let u6 : (¬ p3740) := (Or.elim h87076 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h96076 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114338 (p2406 p2437 p3032 p3379 p3399 p3740 p4644 : Prop)
    (h105411 : p4644)
    (h91048 : p3399 ∨ (¬ p3032) ∨ (¬ p3740) ∨ (¬ p3379) ∨ (¬ p2406) ∨ (¬ p4644))
    (h96076 : p3740 ∨ p2437)
    : p2437 ∨ p3399 ∨ (¬ p3032) ∨ (¬ p3379) ∨ (¬ p2406) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4644 := h105411;
    let u6 : (¬ p3740) := (Or.elim h91048 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96076 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114340 (p2252 p2396 p2417 p2437 p2727 p2807 p3740 : Prop)
    (h99172 : p2417 ∨ (¬ p2396) ∨ p2807 ∨ (¬ p2252) ∨ (¬ p2727) ∨ (¬ p3740))
    (h96076 : p3740 ∨ p2437)
    : p2437 ∨ p2417 ∨ p2807 ∨ (¬ p2396) ∨ (¬ p2252) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p3740) := (Or.elim h99172 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h96076 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114364 (p2246 p2264 p2437 p2459 p2608 p2663 p3073 p3389 p3740 p3830 p5693 : Prop)
    (h110493 : (¬ p3073) ∨ (¬ p5693) ∨ (¬ p3389) ∨ (¬ p2264) ∨ p3830 ∨ (¬ p2663) ∨ (¬ p2246) ∨ (¬ p3740) ∨ (¬ p2608) ∨ (¬ p2459))
    (h96076 : p3740 ∨ p2437)
    : p2437 ∨ (¬ p3073) ∨ (¬ p5693) ∨ (¬ p3389) ∨ (¬ p2264) ∨ p3830 ∨ (¬ p2663) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p3740) := (Or.elim h110493 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u9))))))))))))))))))));
    (Or.elim h96076 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114370 (p2352 p3564 p3746 p3990 : Prop)
    (h111505 : p3564 ∨ (¬ p3746) ∨ (¬ p2352) ∨ (¬ p3990))
    (h102055 : p3746 ∨ p3564)
    : p3564 ∨ (¬ p2352) ∨ (¬ p3990) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3746) := (Or.elim h111505 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h102055 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114371 (p2187 p3550 p4042 p4441 : Prop)
    (h28032 : (¬ p3550) ∨ p4042 ∨ (¬ p4441))
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ p4042 ∨ (¬ p3550) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4042) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4441) := (Or.elim h28032 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h93560 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114372 (p2187 p2363 p3146 p4441 : Prop)
    (h97002 : (¬ p4441) ∨ p3146 ∨ (¬ p2363))
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ p3146 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4441) := (Or.elim h97002 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h93560 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114374 (p2187 p2619 p2860 p3125 p4441 : Prop)
    (h107135 : p3125 ∨ p2860 ∨ (¬ p4441) ∨ (¬ p2619))
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ (¬ p2619) ∨ p2860 ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4441) := (Or.elim h107135 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u1))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114375 (p2187 p2383 p2619 p2860 p4441 : Prop)
    (h83353 : (¬ p2619) ∨ p2860 ∨ p2383 ∨ (¬ p4441))
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ p2860 ∨ (¬ p2619) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2860) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4441) := (Or.elim h83353 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => r2))))));
    (Or.elim h93560 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114377 (p2187 p2373 p2383 p2563 p4441 : Prop)
    (h98393 : (¬ p2373) ∨ p2383 ∨ p2563 ∨ (¬ p4441))
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ p2563 ∨ (¬ p2373) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4441) := (Or.elim h98393 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => r2))))));
    (Or.elim h93560 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114379 (p2187 p2274 p2284 p3156 p4405 p4441 : Prop)
    (h105512 : p4405)
    (h77997 : (¬ p3156) ∨ p2284 ∨ p2274 ∨ (¬ p4405) ∨ (¬ p4441))
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ p2274 ∨ p2284 ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4405 := h105512;
    let u5 : (¬ p4441) := (Or.elim h77997 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114380 (p2187 p2307 p2383 p2459 p3146 p4441 : Prop)
    (h78401 : (¬ p2307) ∨ (¬ p4441) ∨ p2383 ∨ (¬ p2459) ∨ p3146)
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ p3146 ∨ (¬ p2459) ∨ (¬ p2307) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4441) := (Or.elim h78401 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114384 (p2187 p2295 p2619 p2668 p2860 p4441 : Prop)
    (h79418 : (¬ p2295) ∨ (¬ p2619) ∨ (¬ p4441) ∨ p2860 ∨ p2668)
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ (¬ p2619) ∨ (¬ p2295) ∨ p2860 ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4441) := (Or.elim h79418 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114387 (p2166 p2187 p2192 p2363 p2563 p4441 : Prop)
    (h80059 : (¬ p4441) ∨ (¬ p2166) ∨ (¬ p2363) ∨ p2192 ∨ (¬ p2563))
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ (¬ p2166) ∨ (¬ p2563) ∨ p2192 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4441) := (Or.elim h80059 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114388 (p2166 p2187 p2192 p2352 p3958 p4441 : Prop)
    (h105378 : p3958)
    (h80060 : (¬ p4441) ∨ p2192 ∨ (¬ p2166) ∨ (¬ p3958) ∨ p2352)
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ p2192 ∨ p2352 ∨ (¬ p2166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2192) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3958 := h105378;
    let u5 : (¬ p4441) := (Or.elim h80060 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114389 (p2166 p2187 p2192 p2274 p4405 p4441 : Prop)
    (h105512 : p4405)
    (h80062 : (¬ p2166) ∨ p2192 ∨ (¬ p4405) ∨ (¬ p4441) ∨ p2274)
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ p2274 ∨ (¬ p2166) ∨ p2192 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4405 := h105512;
    let u5 : (¬ p4441) := (Or.elim h80062 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114390 (p2187 p2274 p2619 p2860 p4405 p4441 : Prop)
    (h105512 : p4405)
    (h83305 : (¬ p2619) ∨ p2860 ∨ p2274 ∨ (¬ p4405) ∨ (¬ p4441))
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ (¬ p2619) ∨ p2860 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4405 := h105512;
    let u5 : (¬ p4441) := (Or.elim h83305 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114391 (p2156 p2187 p2220 p2363 p2563 p4441 : Prop)
    (h85391 : (¬ p4441) ∨ p2156 ∨ (¬ p2363) ∨ (¬ p2563) ∨ (¬ p2220))
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ (¬ p2220) ∨ (¬ p2363) ∨ (¬ p2563) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4441) := (Or.elim h85391 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114393 (p2156 p2187 p2220 p2274 p4405 p4441 : Prop)
    (h105512 : p4405)
    (h85419 : (¬ p2220) ∨ p2156 ∨ p2274 ∨ (¬ p4405) ∨ (¬ p4441))
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ p2274 ∨ p2156 ∨ (¬ p2220) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4405 := h105512;
    let u5 : (¬ p4441) := (Or.elim h85419 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114395 (p2187 p2373 p2563 p2819 p4441 p4889 : Prop)
    (h93426 : (¬ p2373) ∨ p2563 ∨ (¬ p4889) ∨ (¬ p4441) ∨ p2819)
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ p2563 ∨ (¬ p2373) ∨ (¬ p4889) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4889 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4441) := (Or.elim h93426 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114397 (p2187 p2373 p2563 p2668 p4441 p4564 : Prop)
    (h105401 : p4564)
    (h98551 : (¬ p2373) ∨ p2563 ∨ (¬ p4441) ∨ (¬ p4564) ∨ p2668)
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ p2563 ∨ (¬ p2373) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4564 := h105401;
    let u5 : (¬ p4441) := (Or.elim h98551 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114399 (p2187 p2284 p2352 p3156 p3958 p4441 : Prop)
    (h105378 : p3958)
    (h98698 : (¬ p4441) ∨ (¬ p3156) ∨ p2352 ∨ p2284 ∨ (¬ p3958))
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ p2284 ∨ (¬ p3156) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3958 := h105378;
    let u5 : (¬ p4441) := (Or.elim h98698 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114401 (p2187 p2373 p2563 p3309 p3923 p4441 : Prop)
    (h98743 : (¬ p2373) ∨ (¬ p4441) ∨ (¬ p3309) ∨ p2563 ∨ (¬ p3923))
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ (¬ p3923) ∨ (¬ p2373) ∨ (¬ p3309) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4441) := (Or.elim h98743 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114402 (p2187 p2363 p2373 p2440 p2459 p4441 : Prop)
    (h98761 : (¬ p2373) ∨ (¬ p4441) ∨ (¬ p2363) ∨ p2459 ∨ p2440)
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ (¬ p2373) ∨ p2459 ∨ (¬ p2363) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4441) := (Or.elim h98761 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114404 (p2187 p2911 p3868 p4133 p4441 p5562 p5568 : Prop)
    (h105712 : p4133)
    (h76644 : (¬ p3868) ∨ (¬ p5568) ∨ (¬ p4133) ∨ (¬ p5562) ∨ p2911 ∨ (¬ p4441))
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ (¬ p3868) ∨ (¬ p5562) ∨ (¬ p5568) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5562 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4133 := h105712;
    let u6 : (¬ p4441) := (Or.elim h76644 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => r4))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114408 (p2187 p2459 p2911 p3146 p3955 p4441 p4712 : Prop)
    (h105422 : p4712)
    (h82406 : (¬ p4441) ∨ (¬ p2911) ∨ (¬ p4712) ∨ (¬ p3955) ∨ (¬ p2459) ∨ p3146)
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ p3146 ∨ (¬ p2911) ∨ (¬ p2459) ∨ (¬ p3955) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4712 := h105422;
    let u6 : (¬ p4441) := (Or.elim h82406 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u1 r4))))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114409 (p2187 p2459 p2619 p3105 p3949 p4133 p4441 : Prop)
    (h105712 : p4133)
    (h84475 : p3105 ∨ (¬ p2619) ∨ (¬ p3949) ∨ (¬ p4441) ∨ (¬ p4133) ∨ (¬ p2459))
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ p3105 ∨ (¬ p3949) ∨ (¬ p2459) ∨ (¬ p2619) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3105) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3949 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4133 := h105712;
    let u6 : (¬ p4441) := (Or.elim h84475 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114410 (p2156 p2187 p2220 p2553 p4203 p4405 p4441 : Prop)
    (h105512 : p4405)
    (h85554 : (¬ p4441) ∨ p2156 ∨ (¬ p2220) ∨ p2553 ∨ (¬ p4203) ∨ (¬ p4405))
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ p2553 ∨ (¬ p2220) ∨ p2156 ∨ (¬ p4203) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4405 := h105512;
    let u6 : (¬ p4441) := (Or.elim h85554 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114411 (p2187 p2619 p2870 p3550 p4441 p5559 p5660 : Prop)
    (h106189 : p5559)
    (h86789 : (¬ p5660) ∨ (¬ p4441) ∨ p2870 ∨ (¬ p2619) ∨ (¬ p3550) ∨ (¬ p5559))
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ (¬ p5660) ∨ (¬ p3550) ∨ p2870 ∨ (¬ p2619) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5559 := h106189;
    let u6 : (¬ p4441) := (Or.elim h86789 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114415 (p2156 p2187 p2363 p2373 p2563 p4399 p4441 : Prop)
    (h98195 : (¬ p4441) ∨ (¬ p2156) ∨ (¬ p2373) ∨ p2563 ∨ (¬ p4399) ∨ (¬ p2363))
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ p2563 ∨ (¬ p2373) ∨ (¬ p2156) ∨ (¬ p2363) ∨ (¬ p4399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4441) := (Or.elim h98195 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114421 (p2187 p2373 p2563 p3309 p4356 p4405 p4441 p5016 : Prop)
    (h105512 : p4405)
    (h91794 : (¬ p5016) ∨ (¬ p4441) ∨ (¬ p4405) ∨ p2563 ∨ (¬ p4356) ∨ (¬ p2373) ∨ p3309)
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ p2563 ∨ p3309 ∨ (¬ p2373) ∨ (¬ p4356) ∨ (¬ p5016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4405 := h105512;
    let u7 : (¬ p4441) := (Or.elim h91794 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (u2 r5))))))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114423 (p2156 p2187 p2957 p3156 p3955 p4393 p4441 p5472 : Prop)
    (h96114 : (¬ p4393) ∨ (¬ p4441) ∨ (¬ p5472) ∨ (¬ p2957) ∨ p2156 ∨ (¬ p3156) ∨ (¬ p3955))
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ (¬ p5472) ∨ (¬ p4393) ∨ (¬ p2957) ∨ (¬ p3955) ∨ p2156 ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5472 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4441) := (Or.elim h96114 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u4))))))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114428 (p2187 p2563 p3156 p3737 p3955 p4153 p4328 p4329 p4441 : Prop)
    (h46089 : (¬ p2563) ∨ (¬ p3156) ∨ (¬ p3737) ∨ (¬ p3955) ∨ (¬ p4153) ∨ (¬ p4328) ∨ (¬ p4329) ∨ (¬ p4441))
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ (¬ p3737) ∨ (¬ p4329) ∨ (¬ p3156) ∨ (¬ p2563) ∨ (¬ p4328) ∨ (¬ p4153) ∨ (¬ p3955) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4329 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4441) := (Or.elim h46089 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => r6))))))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114431 (p2156 p2187 p2241 p2264 p2373 p2563 p2996 p4133 p4441 p4521 : Prop)
    (h105712 : p4133)
    (h80868 : (¬ p4441) ∨ (¬ p2996) ∨ p2241 ∨ p2264 ∨ (¬ p2156) ∨ (¬ p4521) ∨ (¬ p2373) ∨ p2563 ∨ (¬ p4133))
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ p2563 ∨ (¬ p2373) ∨ (¬ p2156) ∨ p2264 ∨ (¬ p2996) ∨ p2241 ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4133 := h105712;
    let u9 : (¬ p4441) := (Or.elim h80868 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u1 q7))) (fun r7 => (False.elim (r7 u8))))))))))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114432 (p2156 p2187 p2373 p2563 p2608 p2707 p2717 p4133 p4441 p4521 : Prop)
    (h105712 : p4133)
    (h88270 : (¬ p2373) ∨ (¬ p4441) ∨ p2563 ∨ p2717 ∨ p2707 ∨ (¬ p4133) ∨ p2608 ∨ (¬ p2156) ∨ (¬ p4521))
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ p2563 ∨ p2717 ∨ (¬ p4521) ∨ p2707 ∨ (¬ p2156) ∨ (¬ p2373) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4133 := h105712;
    let u9 : (¬ p4441) := (Or.elim h88270 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u3))))))))))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114433 (p2139 p2156 p2187 p2284 p2598 p2911 p3156 p3201 p4133 p4441 : Prop)
    (h105712 : p4133)
    (h95651 : (¬ p3156) ∨ p2284 ∨ (¬ p4441) ∨ p2911 ∨ p2598 ∨ (¬ p2156) ∨ (¬ p4133) ∨ (¬ p2139) ∨ p3201)
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ p2284 ∨ (¬ p3156) ∨ (¬ p2156) ∨ p2598 ∨ p2911 ∨ p3201 ∨ (¬ p2139) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4133 := h105712;
    let u9 : (¬ p4441) := (Or.elim h95651 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (u6 r7))))))))))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114434 (p2098 p2139 p2156 p2187 p2373 p2459 p2563 p3609 p4133 p4441 : Prop)
    (h105712 : p4133)
    (h97141 : (¬ p4441) ∨ p2098 ∨ (¬ p4133) ∨ (¬ p2156) ∨ (¬ p2139) ∨ p2563 ∨ p3609 ∨ (¬ p2459) ∨ (¬ p2373))
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ p2098 ∨ (¬ p2156) ∨ (¬ p2373) ∨ (¬ p2459) ∨ p3609 ∨ p2563 ∨ (¬ p2139) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4133 := h105712;
    let u9 : (¬ p4441) := (Or.elim h97141 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u3))))))))))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114439 (p2187 p2383 p2753 p2911 p3146 p3204 p3266 p3425 p4253 p4441 p4512 p4877 p5503 : Prop)
    (h105451 : p4877)
    (h76538 : (¬ p5503) ∨ p3146 ∨ p3425 ∨ (¬ p2911) ∨ p2383 ∨ p3266 ∨ (¬ p2753) ∨ (¬ p4512) ∨ (¬ p4253) ∨ (¬ p4441) ∨ (¬ p3204) ∨ (¬ p4877))
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ p3266 ∨ (¬ p4512) ∨ p3146 ∨ (¬ p2911) ∨ p3425 ∨ (¬ p2753) ∨ p2383 ∨ (¬ p3204) ∨ (¬ p5503) ∨ (¬ p4253) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4877 := h105451;
    let u12 : (¬ p4441) := (Or.elim h76538 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => q9) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u8))) (fun r10 => (False.elim (r10 u11))))))))))))))))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114440 (p2187 p2383 p2598 p2753 p3146 p3201 p3204 p3266 p3868 p4441 p4512 p4826 p4877 : Prop)
    (h105451 : p4877)
    (h105444 : p4826)
    (h77235 : p3266 ∨ p3146 ∨ (¬ p4877) ∨ (¬ p3868) ∨ (¬ p2753) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3204) ∨ (¬ p4441) ∨ (¬ p4512) ∨ p2383 ∨ (¬ p4826))
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ (¬ p3868) ∨ p3266 ∨ p3146 ∨ p2383 ∨ (¬ p3201) ∨ (¬ p2753) ∨ (¬ p2598) ∨ (¬ p4512) ∨ (¬ p3204) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4877 := h105451;
    let u11 : p4826 := h105444;
    let u12 : (¬ p4441) := (Or.elim h77235 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => q8) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (u4 q10))) (fun r10 => (False.elim (r10 u11))))))))))))))))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114441 (p2144 p2156 p2187 p2252 p2459 p2528 p2619 p2655 p2750 p2753 p2860 p3389 p4133 p4186 p4441 : Prop)
    (h106345 : p2750)
    (h105712 : p4133)
    (h101671 : p2860 ∨ (¬ p4186) ∨ (¬ p2156) ∨ p2528 ∨ (¬ p2655) ∨ (¬ p2252) ∨ (¬ p4441) ∨ (¬ p4133) ∨ (¬ p2459) ∨ (¬ p2619) ∨ (¬ p2753) ∨ (¬ p2144) ∨ p3389 ∨ (¬ p2750))
    (h93560 : p4441 ∨ (¬ p2187))
    : (¬ p2187) ∨ (¬ p2459) ∨ p2528 ∨ p3389 ∨ p2860 ∨ (¬ p2156) ∨ (¬ p2753) ∨ (¬ p2655) ∨ (¬ p2619) ∨ (¬ p2144) ∨ (¬ p2252) ∨ (¬ p4186) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4186 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p2750 := h106345;
    let u13 : p4133 := h105712;
    let u14 : (¬ p4441) := (Or.elim h101671 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u13))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u6))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u9))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (u3 q12))) (fun r12 => (False.elim (r12 u12))))))))))))))))))))))))))));
    (Or.elim h93560 (fun q0 => (False.elim (u14 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114442 (p2881 p3693 p4132 p4383 : Prop)
    (h35557 : (¬ p3693) ∨ (¬ p4132) ∨ p4383)
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ p4383 ∨ (¬ p3693) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4383) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4132) := (Or.elim h35557 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h95081 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114443 (p2459 p2881 p3146 p4132 : Prop)
    (h113021 : p2459 ∨ (¬ p4132) ∨ (¬ p3146))
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ p2459 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4132) := (Or.elim h113021 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h95081 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114445 (p2166 p2341 p2881 p2891 p4132 : Prop)
    (h75967 : (¬ p2891) ∨ (¬ p2341) ∨ (¬ p4132) ∨ p2166)
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ p2166 ∨ (¬ p2341) ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4132) := (Or.elim h75967 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (u1 r2))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114446 (p2341 p2373 p2427 p2881 p4132 : Prop)
    (h78906 : (¬ p2341) ∨ p2373 ∨ (¬ p4132) ∨ (¬ p2427))
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ p2373 ∨ (¬ p2341) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4132) := (Or.elim h78906 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114449 (p2373 p2881 p2911 p3741 p4132 : Prop)
    (h101897 : (¬ p3741) ∨ (¬ p2911) ∨ (¬ p4132) ∨ p2373)
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ p2373 ∨ (¬ p2911) ∨ (¬ p3741) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4132) := (Or.elim h101897 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (u1 r2))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114452 (p2166 p2264 p2881 p2891 p4132 p4362 : Prop)
    (h106173 : p4362)
    (h75971 : (¬ p2891) ∨ (¬ p2264) ∨ (¬ p4362) ∨ p2166 ∨ (¬ p4132))
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ p2166 ∨ (¬ p2264) ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4362 := h106173;
    let u5 : (¬ p4132) := (Or.elim h75971 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => r3))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114453 (p2166 p2177 p2881 p2891 p4132 p4556 : Prop)
    (h105399 : p4556)
    (h75982 : (¬ p2891) ∨ (¬ p4556) ∨ (¬ p2177) ∨ (¬ p4132) ∨ p2166)
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ p2166 ∨ (¬ p2177) ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4556 := h105399;
    let u5 : (¬ p4132) := (Or.elim h75982 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114454 (p2166 p2881 p2891 p3246 p4132 p4668 : Prop)
    (h105414 : p4668)
    (h75985 : (¬ p2891) ∨ (¬ p3246) ∨ (¬ p4132) ∨ p2166 ∨ (¬ p4668))
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ (¬ p3246) ∨ p2166 ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2166) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4668 := h105414;
    let u5 : (¬ p4132) := (Or.elim h75985 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114455 (p2166 p2427 p2459 p2881 p2891 p4132 : Prop)
    (h75989 : (¬ p4132) ∨ (¬ p2891) ∨ p2427 ∨ p2459 ∨ p2166)
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ p2459 ∨ p2166 ∨ p2427 ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2166) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4132) := (Or.elim h75989 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114456 (p2373 p2427 p2881 p3246 p4132 p4668 : Prop)
    (h105414 : p4668)
    (h78901 : (¬ p3246) ∨ p2373 ∨ (¬ p4132) ∨ (¬ p4668) ∨ (¬ p2427))
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ p2373 ∨ (¬ p3246) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4668 := h105414;
    let u5 : (¬ p4132) := (Or.elim h78901 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114457 (p2177 p2373 p2427 p2881 p4132 p4556 : Prop)
    (h105399 : p4556)
    (h78904 : (¬ p2427) ∨ (¬ p4132) ∨ (¬ p4556) ∨ p2373 ∨ (¬ p2177))
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ p2373 ∨ (¬ p2427) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4556 := h105399;
    let u5 : (¬ p4132) := (Or.elim h78904 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114458 (p2264 p2373 p2427 p2881 p4132 p4362 : Prop)
    (h106173 : p4362)
    (h78905 : (¬ p2427) ∨ (¬ p2264) ∨ (¬ p4132) ∨ (¬ p4362) ∨ p2373)
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ p2373 ∨ (¬ p2264) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4362 := h106173;
    let u5 : (¬ p4132) := (Or.elim h78905 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114460 (p2881 p2901 p3156 p4129 p4132 p5564 : Prop)
    (h79045 : (¬ p4129) ∨ (¬ p5564) ∨ p3156 ∨ (¬ p2901) ∨ (¬ p4132))
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ (¬ p5564) ∨ (¬ p4129) ∨ p3156 ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4129 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4132) := (Or.elim h79045 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114461 (p2177 p2881 p2901 p3156 p4132 p4556 : Prop)
    (h105399 : p4556)
    (h79089 : (¬ p2901) ∨ (¬ p4132) ∨ (¬ p4556) ∨ p3156 ∨ (¬ p2177))
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ p3156 ∨ (¬ p2177) ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4556 := h105399;
    let u5 : (¬ p4132) := (Or.elim h79089 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114462 (p2881 p2901 p2911 p3156 p4132 p4647 : Prop)
    (h105412 : p4647)
    (h79104 : (¬ p2911) ∨ (¬ p2901) ∨ (¬ p4647) ∨ (¬ p4132) ∨ p3156)
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ (¬ p2911) ∨ p3156 ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4647 := h105412;
    let u5 : (¬ p4132) := (Or.elim h79104 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114463 (p2220 p2881 p3051 p4129 p4132 p5564 : Prop)
    (h80272 : (¬ p4129) ∨ (¬ p5564) ∨ p2220 ∨ (¬ p4132) ∨ (¬ p3051))
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ (¬ p5564) ∨ (¬ p4129) ∨ p2220 ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4129 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4132) := (Or.elim h80272 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114464 (p2619 p2870 p2881 p2911 p4132 p4647 : Prop)
    (h105412 : p4647)
    (h84619 : (¬ p2870) ∨ (¬ p2911) ∨ (¬ p4132) ∨ p2619 ∨ (¬ p4647))
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ p2619 ∨ (¬ p2911) ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4647 := h105412;
    let u5 : (¬ p4132) := (Or.elim h84619 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114465 (p2459 p2619 p2870 p2881 p3051 p4132 : Prop)
    (h84620 : (¬ p2870) ∨ p3051 ∨ p2459 ∨ (¬ p4132) ∨ p2619)
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ p2459 ∨ (¬ p2870) ∨ p3051 ∨ p2619 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4132) := (Or.elim h84620 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114466 (p2177 p2619 p2870 p2881 p4132 p4556 : Prop)
    (h105399 : p4556)
    (h84775 : (¬ p2870) ∨ (¬ p4132) ∨ (¬ p2177) ∨ (¬ p4556) ∨ p2619)
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ p2619 ∨ (¬ p2177) ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4556 := h105399;
    let u5 : (¬ p4132) := (Or.elim h84775 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114467 (p2717 p2881 p2901 p3156 p4132 p4898 : Prop)
    (h105455 : p4898)
    (h89264 : (¬ p2901) ∨ (¬ p2717) ∨ (¬ p4898) ∨ (¬ p4132) ∨ p3156)
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ (¬ p2717) ∨ p3156 ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4898 := h105455;
    let u5 : (¬ p4132) := (Or.elim h89264 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114468 (p2177 p2220 p2881 p3051 p4132 p4556 : Prop)
    (h105399 : p4556)
    (h92454 : (¬ p3051) ∨ (¬ p4556) ∨ (¬ p4132) ∨ p2220 ∨ (¬ p2177))
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ (¬ p3051) ∨ p2220 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4556 := h105399;
    let u5 : (¬ p4132) := (Or.elim h92454 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114469 (p2220 p2881 p2911 p3051 p4132 p4647 : Prop)
    (h105412 : p4647)
    (h92456 : (¬ p3051) ∨ (¬ p2911) ∨ (¬ p4132) ∨ p2220 ∨ (¬ p4647))
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ p2220 ∨ (¬ p2911) ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4647 := h105412;
    let u5 : (¬ p4132) := (Or.elim h92456 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114470 (p2210 p2881 p3449 p3969 p4132 p5693 : Prop)
    (h94221 : (¬ p5693) ∨ p3449 ∨ (¬ p2210) ∨ (¬ p4132) ∨ (¬ p3969))
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ (¬ p5693) ∨ (¬ p3969) ∨ (¬ p2210) ∨ p3449 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4132) := (Or.elim h94221 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114473 (p2177 p2619 p2881 p3105 p3246 p4132 : Prop)
    (h111070 : p3246 ∨ (¬ p4132) ∨ p2619 ∨ (¬ p2177) ∨ (¬ p3105))
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ p3246 ∨ p2619 ∨ (¬ p2177) ∨ (¬ p3105) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4132) := (Or.elim h111070 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114477 (p2341 p2881 p2901 p3156 p3575 p4132 p4647 : Prop)
    (h105412 : p4647)
    (h79080 : (¬ p2901) ∨ (¬ p2341) ∨ (¬ p4647) ∨ (¬ p3575) ∨ (¬ p4132) ∨ p3156)
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ p3156 ∨ (¬ p2341) ∨ (¬ p2901) ∨ (¬ p3575) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4647 := h105412;
    let u6 : (¬ p4132) := (Or.elim h79080 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (u1 r4))))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114480 (p2619 p2870 p2881 p3516 p3691 p4132 p4668 : Prop)
    (h105414 : p4668)
    (h84621 : (¬ p3516) ∨ p2619 ∨ (¬ p4132) ∨ (¬ p4668) ∨ (¬ p3691) ∨ (¬ p2870))
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ (¬ p3516) ∨ p2619 ∨ (¬ p2870) ∨ (¬ p3691) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4668 := h105414;
    let u6 : (¬ p4132) := (Or.elim h84621 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114483 (p2449 p2881 p3919 p3969 p4132 p4668 p5600 : Prop)
    (h105414 : p4668)
    (h56563 : (¬ p2449) ∨ (¬ p3919) ∨ (¬ p3969) ∨ (¬ p4132) ∨ (¬ p4668) ∨ (¬ p5600))
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ (¬ p2449) ∨ (¬ p5600) ∨ (¬ p3969) ∨ (¬ p3919) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4668 := h105414;
    let u6 : (¬ p4132) := (Or.elim h56563 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114486 (p2177 p2881 p3073 p3146 p3919 p4132 p4288 : Prop)
    (h93663 : p3073 ∨ (¬ p4288) ∨ (¬ p3919) ∨ (¬ p4132) ∨ (¬ p2177) ∨ (¬ p3146))
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ (¬ p3146) ∨ (¬ p2177) ∨ (¬ p3919) ∨ p3073 ∨ (¬ p4288) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4288 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4132) := (Or.elim h93663 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114488 (p2881 p2951 p3051 p3156 p3246 p4132 p4668 : Prop)
    (h105414 : p4668)
    (h98239 : p3156 ∨ (¬ p3246) ∨ (¬ p4132) ∨ (¬ p4668) ∨ (¬ p3051) ∨ (¬ p2951))
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ (¬ p3246) ∨ (¬ p3051) ∨ p3156 ∨ (¬ p2951) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4668 := h105414;
    let u6 : (¬ p4132) := (Or.elim h98239 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114489 (p2088 p2881 p3146 p3961 p4063 p4132 p5564 : Prop)
    (h98445 : (¬ p5564) ∨ p2088 ∨ (¬ p4063) ∨ (¬ p3961) ∨ (¬ p3146) ∨ (¬ p4132))
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ (¬ p5564) ∨ (¬ p4063) ∨ p2088 ∨ (¬ p3146) ∨ (¬ p3961) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3961 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4132) := (Or.elim h98445 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => r4))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114490 (p2717 p2881 p3434 p3969 p4132 p4445 p5122 : Prop)
    (h105483 : p5122)
    (h102382 : p3434 ∨ (¬ p2717) ∨ (¬ p4445) ∨ (¬ p5122) ∨ (¬ p3969) ∨ (¬ p4132))
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ (¬ p3969) ∨ (¬ p4445) ∨ p3434 ∨ (¬ p2717) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5122 := h105483;
    let u6 : (¬ p4132) := (Or.elim h102382 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => r4))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114494 (p2264 p2881 p3146 p3189 p3848 p4132 p5107 : Prop)
    (h112912 : p2264 ∨ (¬ p5107) ∨ (¬ p3189) ∨ (¬ p4132) ∨ (¬ p3146) ∨ (¬ p3848))
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ p2264 ∨ (¬ p5107) ∨ (¬ p3189) ∨ (¬ p3146) ∨ (¬ p3848) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2264) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3848 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4132) := (Or.elim h112912 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114510 (p2341 p2608 p2881 p3093 p3146 p3266 p3543 p4132 p4435 p4793 p5254 : Prop)
    (h105438 : p4793)
    (h96704 : (¬ p4435) ∨ (¬ p4793) ∨ (¬ p2608) ∨ p3093 ∨ (¬ p5254) ∨ (¬ p3146) ∨ (¬ p4132) ∨ (¬ p2341) ∨ (¬ p3543) ∨ (¬ p3266))
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ (¬ p4435) ∨ (¬ p5254) ∨ (¬ p3146) ∨ p3093 ∨ (¬ p3266) ∨ (¬ p3543) ∨ (¬ p2341) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3543 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4793 := h105438;
    let u10 : (¬ p4132) := (Or.elim h96704 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u5))))))))))))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114513 (p2341 p2696 p2797 p2881 p3146 p3266 p3366 p3370 p4132 p4228 p4988 p5254 : Prop)
    (h110237 : p4228 ∨ (¬ p3146) ∨ (¬ p5254) ∨ p2797 ∨ (¬ p3266) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p2341) ∨ (¬ p4132) ∨ (¬ p4988) ∨ p2696)
    (h95081 : p4132 ∨ p2881)
    : p2881 ∨ p4228 ∨ (¬ p3146) ∨ (¬ p5254) ∨ p2797 ∨ (¬ p3266) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p2341) ∨ (¬ p4988) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4228) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p4132) := (Or.elim h110237 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => q8) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (False.elim (u10 r9))))))))))))))))))))));
    (Or.elim h95081 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114514 (p2509 p4370 p4683 p5866 : Prop)
    (h113023 : (¬ p4683) ∨ (¬ p5866) ∨ (¬ p4370) ∨ (¬ p2509))
    (h7549 : p4370 ∨ (¬ p4683))
    : (¬ p4683) ∨ (¬ p5866) ∨ (¬ p2509) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4683 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5866 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4370) := (Or.elim h113023 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h7549 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114515 (p2911 p3201 p3641 p4186 : Prop)
    (h77349 : p3201 ∨ (¬ p3641) ∨ (¬ p4186))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ p3201 ∨ (¬ p3641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4186) := (Or.elim h77349 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h91169 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114516 (p2470 p2911 p3389 p4186 : Prop)
    (h77493 : p3389 ∨ (¬ p2470) ∨ (¬ p4186))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ (¬ p2470) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4186) := (Or.elim h77493 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => r1))));
    (Or.elim h91169 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114517 (p2518 p2911 p2922 p4186 : Prop)
    (h35053 : (¬ p2518) ∨ p2922 ∨ (¬ p4186))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ p2922 ∨ (¬ p2518) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2922) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4186) := (Or.elim h35053 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h91169 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114518 (p2437 p2911 p3083 p4186 : Prop)
    (h97015 : (¬ p3083) ∨ p2437 ∨ (¬ p4186))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ (¬ p3083) ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4186) := (Or.elim h97015 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h91169 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114519 (p2911 p3573 p3581 p4186 : Prop)
    (h32074 : p3573 ∨ (¬ p3581) ∨ (¬ p4186))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ p3573 ∨ (¬ p3581) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4186) := (Or.elim h32074 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h91169 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114520 (p2441 p2911 p4186 p4607 : Prop)
    (h40662 : (¬ p2441) ∨ (¬ p4186) ∨ p4607)
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ p4607 ∨ (¬ p2441) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4607) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4186) := (Or.elim h40662 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h91169 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114521 (p2528 p2911 p4186 p4635 : Prop)
    (h112465 : p2528 ∨ p4635 ∨ (¬ p4186))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ p2528 ∨ p4635 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p4635) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4186) := (Or.elim h112465 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h91169 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114526 (p2459 p2911 p3389 p3941 p4149 p4186 : Prop)
    (h89935 : p4149 ∨ (¬ p4186) ∨ p2459 ∨ p3389 ∨ (¬ p3941))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ p4149 ∨ (¬ p3941) ∨ p2459 ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4149) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4186) := (Or.elim h89935 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h91169 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114527 (p2341 p2459 p2528 p2911 p4186 p5203 : Prop)
    (h105490 : p5203)
    (h101666 : p2528 ∨ (¬ p2341) ∨ (¬ p4186) ∨ (¬ p5203) ∨ (¬ p2459))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ p2528 ∨ (¬ p2459) ∨ (¬ p2341) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5203 := h105490;
    let u5 : (¬ p4186) := (Or.elim h101666 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h91169 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114528 (p2459 p2528 p2573 p2911 p3389 p4186 : Prop)
    (h101669 : p3389 ∨ (¬ p4186) ∨ (¬ p2459) ∨ (¬ p2573) ∨ p2528)
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ p2528 ∨ (¬ p2459) ∨ (¬ p2573) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4186) := (Or.elim h101669 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h91169 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114529 (p2459 p2528 p2598 p2911 p3201 p4186 : Prop)
    (h101681 : p3201 ∨ (¬ p4186) ∨ p2528 ∨ (¬ p2459) ∨ p2598)
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ p2528 ∨ p3201 ∨ p2598 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4186) := (Or.elim h101681 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h91169 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114530 (p2437 p2459 p2528 p2651 p2911 p4186 : Prop)
    (h101685 : p2528 ∨ (¬ p4186) ∨ p2437 ∨ p2651 ∨ (¬ p2459))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ p2528 ∨ (¬ p2459) ∨ p2437 ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4186) := (Or.elim h101685 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h91169 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114532 (p2528 p2911 p2922 p3609 p3641 p4186 : Prop)
    (h110399 : (¬ p3641) ∨ (¬ p3609) ∨ p2528 ∨ (¬ p4186) ∨ p2922)
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ (¬ p3641) ∨ (¬ p3609) ∨ p2528 ∨ p2922 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4186) := (Or.elim h110399 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h91169 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114533 (p2850 p2911 p3641 p4019 p4149 p4186 : Prop)
    (h110401 : (¬ p3641) ∨ (¬ p4019) ∨ p4149 ∨ p2850 ∨ (¬ p4186))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ (¬ p3641) ∨ (¬ p4019) ∨ p4149 ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p4149) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4186) := (Or.elim h110401 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => r3))))))));
    (Or.elim h91169 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114534 (p2459 p2528 p2911 p3363 p3367 p3389 p4186 : Prop)
    (h75572 : p2528 ∨ p3389 ∨ (¬ p2459) ∨ p3367 ∨ (¬ p4186) ∨ (¬ p3363))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ (¬ p3363) ∨ p2528 ∨ p3389 ∨ p3367 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4186) := (Or.elim h75572 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h91169 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114536 (p2088 p2528 p2881 p2911 p3960 p4186 p4277 : Prop)
    (h105380 : p4277)
    (h78463 : p2528 ∨ (¬ p2881) ∨ (¬ p4186) ∨ (¬ p2088) ∨ (¬ p4277) ∨ (¬ p3960))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ (¬ p2088) ∨ (¬ p2881) ∨ (¬ p3960) ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4277 := h105380;
    let u6 : (¬ p4186) := (Or.elim h78463 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h91169 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114537 (p2441 p2528 p2911 p3146 p3156 p4186 p4705 : Prop)
    (h106238 : p4705)
    (h78773 : p2528 ∨ (¬ p3146) ∨ (¬ p4186) ∨ (¬ p4705) ∨ (¬ p3156) ∨ (¬ p2441))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ (¬ p3156) ∨ p2528 ∨ (¬ p3146) ∨ (¬ p2441) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4705 := h106238;
    let u6 : (¬ p4186) := (Or.elim h78773 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u4))))))))))));
    (Or.elim h91169 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114538 (p2437 p2528 p2911 p3073 p4186 p4688 p4814 : Prop)
    (h105440 : p4814)
    (h80174 : (¬ p4688) ∨ (¬ p3073) ∨ (¬ p4186) ∨ p2528 ∨ p2437 ∨ (¬ p4814))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ (¬ p4688) ∨ (¬ p3073) ∨ p2528 ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p4688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4814 := h105440;
    let u6 : (¬ p4186) := (Or.elim h80174 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h91169 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114540 (p2437 p2440 p2459 p2911 p3146 p3693 p4186 : Prop)
    (h83110 : p2440 ∨ p3146 ∨ (¬ p3693) ∨ (¬ p4186) ∨ (¬ p2459) ∨ p2437)
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ p3146 ∨ (¬ p2459) ∨ p2440 ∨ p2437 ∨ (¬ p3693) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4186) := (Or.elim h83110 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (u4 r4))))))))))));
    (Or.elim h91169 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114543 (p2707 p2911 p3083 p3367 p4106 p4186 p4750 : Prop)
    (h105433 : p4750)
    (h101321 : p2707 ∨ (¬ p4106) ∨ (¬ p3367) ∨ (¬ p4186) ∨ (¬ p4750) ∨ (¬ p3083))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ (¬ p3083) ∨ p2707 ∨ (¬ p3367) ∨ (¬ p4106) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4106 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4750 := h105433;
    let u6 : (¬ p4186) := (Or.elim h101321 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h91169 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114544 (p2363 p2528 p2911 p3868 p4105 p4186 p4442 : Prop)
    (h101498 : (¬ p4442) ∨ p2528 ∨ (¬ p2363) ∨ (¬ p3868) ∨ (¬ p4105) ∨ (¬ p4186))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ (¬ p4442) ∨ (¬ p3868) ∨ p2528 ∨ (¬ p2363) ∨ (¬ p4105) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p4442 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4186) := (Or.elim h101498 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h91169 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114545 (p2459 p2528 p2662 p2727 p2911 p3389 p4186 : Prop)
    (h101664 : p2528 ∨ p2727 ∨ (¬ p4186) ∨ (¬ p2662) ∨ p3389 ∨ (¬ p2459))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ p3389 ∨ p2528 ∨ (¬ p2662) ∨ p2727 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4186) := (Or.elim h101664 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h91169 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114547 (p2098 p2437 p2440 p2598 p2911 p3641 p4186 : Prop)
    (h111134 : (¬ p3641) ∨ (¬ p2098) ∨ p2437 ∨ p2440 ∨ p2598 ∨ (¬ p4186))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ (¬ p3641) ∨ (¬ p2098) ∨ p2437 ∨ p2440 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4186) := (Or.elim h111134 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => r4))))))))));
    (Or.elim h91169 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114554 (p2911 p3654 p3998 p4114 p4149 p4186 p4620 p4710 : Prop)
    (h89956 : p4149 ∨ (¬ p3998) ∨ (¬ p4710) ∨ (¬ p4186) ∨ p3654 ∨ (¬ p4620) ∨ (¬ p4114))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ (¬ p3998) ∨ p3654 ∨ p4149 ∨ (¬ p4710) ∨ (¬ p4114) ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p4149) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4114 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4186) := (Or.elim h89956 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u2 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u5))))))))))))));
    (Or.elim h91169 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114564 (p2459 p2528 p2608 p2619 p2839 p2911 p3389 p4186 p4902 p5193 : Prop)
    (h105456 : p4902)
    (h105488 : p5193)
    (h83767 : (¬ p2839) ∨ (¬ p2619) ∨ (¬ p2459) ∨ (¬ p4902) ∨ (¬ p2608) ∨ p2528 ∨ p3389 ∨ (¬ p5193) ∨ (¬ p4186))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ p2528 ∨ p3389 ∨ (¬ p2459) ∨ (¬ p2608) ∨ (¬ p2839) ∨ (¬ p2619) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4902 := h105456;
    let u8 : p5193 := h105488;
    let u9 : (¬ p4186) := (Or.elim h83767 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => r7))))))))))))))));
    (Or.elim h91169 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114565 (p2132 p2187 p2459 p2528 p2860 p2911 p3389 p4133 p4186 p4729 : Prop)
    (h105712 : p4133)
    (h105429 : p4729)
    (h90692 : (¬ p2459) ∨ (¬ p4186) ∨ (¬ p2860) ∨ (¬ p4729) ∨ p2528 ∨ (¬ p2132) ∨ (¬ p2187) ∨ (¬ p4133) ∨ p3389)
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ p2528 ∨ (¬ p2132) ∨ p3389 ∨ (¬ p2187) ∨ (¬ p2459) ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4133 := h105712;
    let u8 : p4729 := h105429;
    let u9 : (¬ p4186) := (Or.elim h90692 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (u3 r7))))))))))))))))));
    (Or.elim h91169 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114567 (p2459 p2528 p2608 p2819 p2829 p2911 p3389 p4133 p4186 p5193 : Prop)
    (h105488 : p5193)
    (h105712 : p4133)
    (h95245 : (¬ p2829) ∨ p2528 ∨ (¬ p4133) ∨ (¬ p5193) ∨ (¬ p2459) ∨ (¬ p2608) ∨ (¬ p4186) ∨ p3389 ∨ (¬ p2819))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ p2528 ∨ (¬ p2459) ∨ (¬ p2819) ∨ p3389 ∨ (¬ p2829) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5193 := h105488;
    let u8 : p4133 := h105712;
    let u9 : (¬ p4186) := (Or.elim h95245 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (False.elim (r7 u3))))))))))))))))));
    (Or.elim h91169 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114568 (p2166 p2210 p2459 p2528 p2608 p2911 p3347 p3389 p4186 p4902 : Prop)
    (h105456 : p4902)
    (h101672 : p3389 ∨ (¬ p4186) ∨ (¬ p3347) ∨ (¬ p2166) ∨ (¬ p4902) ∨ p2528 ∨ (¬ p2459) ∨ p2608 ∨ (¬ p2210))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ (¬ p2166) ∨ p2528 ∨ (¬ p2210) ∨ p3389 ∨ (¬ p3347) ∨ p2608 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4902 := h105456;
    let u9 : (¬ p4186) := (Or.elim h101672 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u2 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u6 q7))) (fun r7 => (False.elim (r7 u3))))))))))))))))));
    (Or.elim h91169 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114572 (p2459 p2528 p2696 p2753 p2911 p3136 p3156 p3347 p3389 p4186 p4902 : Prop)
    (h105456 : p4902)
    (h84323 : (¬ p3156) ∨ p2528 ∨ (¬ p2459) ∨ (¬ p4902) ∨ p3389 ∨ (¬ p3347) ∨ (¬ p4186) ∨ (¬ p3136) ∨ (¬ p2753) ∨ (¬ p2696))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ (¬ p2459) ∨ (¬ p3156) ∨ p2528 ∨ p3389 ∨ (¬ p2696) ∨ (¬ p3136) ∨ (¬ p2753) ∨ (¬ p3347) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4902 := h105456;
    let u10 : (¬ p4186) := (Or.elim h84323 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u5))))))))))))))))))));
    (Or.elim h91169 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114581 (p2246 p2459 p2528 p2727 p2911 p2946 p3005 p3136 p3347 p3389 p4186 p4311 : Prop)
    (h108386 : (¬ p2727) ∨ (¬ p4311) ∨ p2528 ∨ p3389 ∨ p3136 ∨ (¬ p4186) ∨ (¬ p2246) ∨ (¬ p3005) ∨ (¬ p3347) ∨ (¬ p2946) ∨ (¬ p2459))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ (¬ p2727) ∨ (¬ p4311) ∨ p2528 ∨ p3389 ∨ p3136 ∨ (¬ p2246) ∨ (¬ p3005) ∨ (¬ p3347) ∨ (¬ p2946) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p4186) := (Or.elim h108386 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (False.elim (r9 u10))))))))))))))))))))));
    (Or.elim h91169 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114584 (p2252 p2459 p2528 p2608 p2655 p2750 p2911 p3093 p3319 p3322 p3389 p4133 p4186 : Prop)
    (h106345 : p2750)
    (h105712 : p4133)
    (h91871 : (¬ p3322) ∨ (¬ p3319) ∨ p2528 ∨ p3389 ∨ (¬ p2459) ∨ (¬ p4186) ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p3093) ∨ (¬ p2655) ∨ p2608 ∨ (¬ p4133))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ (¬ p3093) ∨ (¬ p3319) ∨ p2528 ∨ p3389 ∨ p2608 ∨ (¬ p2655) ∨ (¬ p2252) ∨ (¬ p3322) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2750 := h106345;
    let u11 : p4133 := h105712;
    let u12 : (¬ p4186) := (Or.elim h91871 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (u5 q10))) (fun r10 => (False.elim (r10 u11))))))))))))))))))))))));
    (Or.elim h91169 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114586 (p2144 p2156 p2187 p2252 p2459 p2528 p2619 p2655 p2753 p2860 p2911 p3389 p4186 : Prop)
    (h114441 : (¬ p2187) ∨ (¬ p2459) ∨ p2528 ∨ p3389 ∨ p2860 ∨ (¬ p2156) ∨ (¬ p2753) ∨ (¬ p2655) ∨ (¬ p2619) ∨ (¬ p2144) ∨ (¬ p2252) ∨ (¬ p4186))
    (h91169 : p4186 ∨ p2911)
    : p2911 ∨ (¬ p2187) ∨ (¬ p2459) ∨ p2528 ∨ p3389 ∨ p2860 ∨ (¬ p2156) ∨ (¬ p2753) ∨ (¬ p2655) ∨ (¬ p2619) ∨ (¬ p2144) ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : (¬ p4186) := (Or.elim h114441 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u11))) (fun r10 => r10))))))))))))))))))))));
    (Or.elim h91169 (fun q0 => (False.elim (u12 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114588 (p2922 p3201 p3590 p4106 : Prop)
    (h111394 : p3201 ∨ (¬ p2922) ∨ (¬ p4106) ∨ (¬ p3590))
    (h97816 : p4106 ∨ p3201)
    : p3201 ∨ (¬ p2922) ∨ (¬ p3590) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4106) := (Or.elim h111394 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h97816 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114589 (p2383 p2482 p2584 p4114 : Prop)
    (h18921 : p2482 ∨ (¬ p2584) ∨ (¬ p4114))
    (h96434 : p4114 ∨ (¬ p2383))
    : (¬ p2383) ∨ p2482 ∨ (¬ p2584) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2482) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4114) := (Or.elim h18921 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h96434 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114590 (p2383 p3178 p3987 p4114 : Prop)
    (h19439 : p3178 ∨ (¬ p3987) ∨ (¬ p4114))
    (h96434 : p4114 ∨ (¬ p2383))
    : (¬ p2383) ∨ p3178 ∨ (¬ p3987) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3178) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4114) := (Or.elim h19439 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    (Or.elim h96434 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114593 (p2307 p2383 p3955 p4113 p4114 : Prop)
    (h78487 : (¬ p4114) ∨ (¬ p4113) ∨ (¬ p3955) ∨ p2307)
    (h96434 : p4114 ∨ (¬ p2383))
    : (¬ p2383) ∨ (¬ p4113) ∨ p2307 ∨ (¬ p3955) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4113 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4114) := (Or.elim h78487 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u2 r2))))))));
    (Or.elim h96434 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114596 (p2088 p2307 p2363 p2383 p4114 p4405 : Prop)
    (h105512 : p4405)
    (h78456 : p2363 ∨ p2307 ∨ (¬ p4114) ∨ (¬ p4405) ∨ (¬ p2088))
    (h96434 : p4114 ∨ (¬ p2383))
    : (¬ p2383) ∨ (¬ p2088) ∨ p2307 ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4405 := h105512;
    let u5 : (¬ p4114) := (Or.elim h78456 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h96434 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114598 (p2088 p2363 p2383 p2788 p2819 p4114 : Prop)
    (h105375 : p2788)
    (h93333 : p2363 ∨ (¬ p2088) ∨ (¬ p2788) ∨ p2819 ∨ (¬ p4114))
    (h96434 : p4114 ∨ (¬ p2383))
    : (¬ p2383) ∨ p2363 ∨ p2819 ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2788 := h105375;
    let u5 : (¬ p4114) := (Or.elim h93333 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => r3))))))));
    (Or.elim h96434 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114599 (p2088 p2363 p2383 p3923 p4114 p5022 : Prop)
    (h105470 : p5022)
    (h96163 : (¬ p4114) ∨ p2363 ∨ (¬ p5022) ∨ (¬ p2088) ∨ (¬ p3923))
    (h96434 : p4114 ∨ (¬ p2383))
    : (¬ p2383) ∨ p2363 ∨ (¬ p3923) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5022 := h105470;
    let u5 : (¬ p4114) := (Or.elim h96163 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h96434 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114602 (p2088 p2352 p2363 p2383 p2507 p4114 p5016 : Prop)
    (h78452 : (¬ p4114) ∨ (¬ p5016) ∨ p2352 ∨ (¬ p2507) ∨ (¬ p2088) ∨ p2363)
    (h96434 : p4114 ∨ (¬ p2383))
    : (¬ p2383) ∨ p2352 ∨ p2363 ∨ (¬ p5016) ∨ (¬ p2507) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2352) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2507 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4114) := (Or.elim h78452 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (u2 r4))))))))))));
    (Or.elim h96434 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114604 (p2088 p2295 p2363 p2383 p3955 p4114 p4584 : Prop)
    (h105406 : p4584)
    (h78468 : (¬ p4114) ∨ (¬ p2088) ∨ (¬ p4584) ∨ p2295 ∨ (¬ p3955) ∨ p2363)
    (h96434 : p4114 ∨ (¬ p2383))
    : (¬ p2383) ∨ p2363 ∨ (¬ p2088) ∨ (¬ p3955) ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4584 := h105406;
    let u6 : (¬ p4114) := (Or.elim h78468 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u1 r4))))))))))));
    (Or.elim h96434 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114605 (p2088 p2274 p2363 p2383 p3743 p4114 p4405 : Prop)
    (h105512 : p4405)
    (h78469 : (¬ p4114) ∨ p2363 ∨ p2274 ∨ (¬ p4405) ∨ (¬ p3743) ∨ (¬ p2088))
    (h96434 : p4114 ∨ (¬ p2383))
    : (¬ p2383) ∨ (¬ p3743) ∨ (¬ p2088) ∨ p2363 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4405 := h105512;
    let u6 : (¬ p4114) := (Or.elim h78469 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h96434 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114606 (p2088 p2274 p2363 p2383 p3955 p4114 p4489 : Prop)
    (h105390 : p4489)
    (h78470 : (¬ p4114) ∨ p2363 ∨ (¬ p3955) ∨ p2274 ∨ (¬ p4489) ∨ (¬ p2088))
    (h96434 : p4114 ∨ (¬ p2383))
    : (¬ p2383) ∨ p2363 ∨ (¬ p2088) ∨ p2274 ∨ (¬ p3955) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4489 := h105390;
    let u6 : (¬ p4114) := (Or.elim h78470 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h96434 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114613 (p2383 p2608 p2819 p2829 p4113 p4114 p5017 : Prop)
    (h90577 : (¬ p4114) ∨ (¬ p5017) ∨ p2608 ∨ p2829 ∨ (¬ p4113) ∨ p2819)
    (h96434 : p4114 ∨ (¬ p2383))
    : (¬ p2383) ∨ p2829 ∨ p2608 ∨ p2819 ∨ (¬ p4113) ∨ (¬ p5017) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4113 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5017 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4114) := (Or.elim h90577 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (u3 r4))))))))))));
    (Or.elim h96434 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114614 (p2088 p2363 p2383 p2630 p2797 p3567 p4114 : Prop)
    (h92262 : p2363 ∨ (¬ p2088) ∨ p2630 ∨ (¬ p3567) ∨ (¬ p4114) ∨ (¬ p2797))
    (h96434 : p4114 ∨ (¬ p2383))
    : (¬ p2383) ∨ (¬ p2797) ∨ (¬ p2088) ∨ p2363 ∨ p2630 ∨ (¬ p3567) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4114) := (Or.elim h92262 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h96434 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114615 (p2088 p2383 p2630 p3567 p3609 p4114 p4364 : Prop)
    (h107419 : (¬ p4364) ∨ (¬ p3567) ∨ (¬ p2088) ∨ (¬ p4114) ∨ p3609 ∨ (¬ p2630))
    (h96434 : p4114 ∨ (¬ p2383))
    : (¬ p2383) ∨ (¬ p4364) ∨ (¬ p2088) ∨ p3609 ∨ (¬ p3567) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4114) := (Or.elim h107419 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96434 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114617 (p2088 p2255 p2383 p3189 p3256 p3987 p4114 : Prop)
    (h105367 : p2255)
    (h100548 : (¬ p4114) ∨ p3256 ∨ (¬ p3987) ∨ (¬ p2255) ∨ p3189 ∨ (¬ p2088))
    (h96434 : p4114 ∨ (¬ p2383))
    : (¬ p2383) ∨ p3256 ∨ (¬ p2088) ∨ p3189 ∨ (¬ p3987) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2255 := h105367;
    let u6 : (¬ p4114) := (Or.elim h100548 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h96434 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114618 (p2088 p2383 p2797 p3073 p3189 p3567 p4114 : Prop)
    (h110255 : p3189 ∨ (¬ p2088) ∨ p3073 ∨ (¬ p3567) ∨ (¬ p4114) ∨ (¬ p2797))
    (h96434 : p4114 ∨ (¬ p2383))
    : (¬ p2383) ∨ p3189 ∨ (¬ p2088) ∨ p3073 ∨ (¬ p3567) ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4114) := (Or.elim h110255 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96434 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114620 (p2088 p2383 p2553 p2578 p2668 p3256 p4114 : Prop)
    (h112355 : (¬ p2668) ∨ (¬ p2088) ∨ (¬ p4114) ∨ (¬ p2578) ∨ p2553 ∨ p3256)
    (h96434 : p4114 ∨ (¬ p2383))
    : (¬ p2383) ∨ (¬ p2668) ∨ (¬ p2088) ∨ (¬ p2578) ∨ p2553 ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4114) := (Or.elim h112355 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (u5 r4))))))))))));
    (Or.elim h96434 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114629 (p2088 p2383 p2891 p3073 p3743 p4114 p4492 p4558 : Prop)
    (h105400 : p4558)
    (h94605 : (¬ p4114) ∨ p3073 ∨ (¬ p3743) ∨ (¬ p4558) ∨ (¬ p4492) ∨ (¬ p2088) ∨ (¬ p2891))
    (h96434 : p4114 ∨ (¬ p2383))
    : (¬ p2383) ∨ p3073 ∨ (¬ p2088) ∨ (¬ p2891) ∨ (¬ p3743) ∨ (¬ p4492) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4492 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4558 := h105400;
    let u7 : (¬ p4114) := (Or.elim h94605 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3))))))))))))));
    (Or.elim h96434 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114640 (p2383 p2911 p3654 p3998 p4114 p4149 p4620 p4710 : Prop)
    (h114554 : p2911 ∨ (¬ p3998) ∨ p3654 ∨ p4149 ∨ (¬ p4710) ∨ (¬ p4114) ∨ (¬ p4620))
    (h96434 : p4114 ∨ (¬ p2383))
    : (¬ p2383) ∨ p2911 ∨ (¬ p3998) ∨ p3654 ∨ p4149 ∨ (¬ p4710) ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2911) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p4149) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4114) := (Or.elim h114554 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (r5 u6))))))))))))));
    (Or.elim h96434 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114644 (p2088 p2383 p2578 p2619 p2870 p3073 p3096 p3537 p4114 : Prop)
    (h112000 : p2619 ∨ (¬ p3537) ∨ p3073 ∨ (¬ p2088) ∨ (¬ p3096) ∨ (¬ p2578) ∨ (¬ p4114) ∨ (¬ p2870))
    (h96434 : p4114 ∨ (¬ p2383))
    : (¬ p2383) ∨ p2619 ∨ (¬ p3537) ∨ p3073 ∨ (¬ p2088) ∨ (¬ p3096) ∨ (¬ p2578) ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4114) := (Or.elim h112000 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (False.elim (r6 u7))))))))))))))));
    (Or.elim h96434 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114648 (p2088 p2254 p2383 p2707 p2881 p2901 p2946 p3537 p3609 p4114 p5020 : Prop)
    (h105366 : p2254)
    (h78489 : p3537 ∨ (¬ p4114) ∨ (¬ p2254) ∨ (¬ p5020) ∨ p2946 ∨ p2901 ∨ p2881 ∨ p3609 ∨ (¬ p2707) ∨ (¬ p2088))
    (h96434 : p4114 ∨ (¬ p2383))
    : (¬ p2383) ∨ (¬ p2707) ∨ p3537 ∨ p2901 ∨ p2946 ∨ p2881 ∨ (¬ p2088) ∨ p3609 ∨ (¬ p5020) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2254 := h105366;
    let u10 : (¬ p4114) := (Or.elim h78489 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u3 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (False.elim (r8 u6))))))))))))))))))));
    (Or.elim h96434 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114650 (p2088 p2363 p2383 p2696 p2748 p2779 p2829 p2992 p3156 p4114 p4134 : Prop)
    (h105379 : p4134)
    (h95716 : (¬ p4114) ∨ p2363 ∨ (¬ p4134) ∨ p2992 ∨ (¬ p2829) ∨ (¬ p2748) ∨ (¬ p2088) ∨ p3156 ∨ p2696 ∨ (¬ p2779))
    (h96434 : p4114 ∨ (¬ p2383))
    : (¬ p2383) ∨ (¬ p2088) ∨ p2992 ∨ (¬ p2779) ∨ p2363 ∨ (¬ p2829) ∨ (¬ p2748) ∨ p3156 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2779 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4134 := h105379;
    let u10 : (¬ p4114) := (Or.elim h95716 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u8 q8))) (fun r8 => (False.elim (r8 u3))))))))))))))))))));
    (Or.elim h96434 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114652 (p2088 p2190 p2241 p2383 p2619 p2870 p2992 p3156 p3609 p4114 p5017 : Prop)
    (h112008 : p2619 ∨ p3156 ∨ p3609 ∨ (¬ p5017) ∨ (¬ p2088) ∨ (¬ p2870) ∨ (¬ p2190) ∨ (¬ p4114) ∨ p2992 ∨ p2241)
    (h96434 : p4114 ∨ (¬ p2383))
    : (¬ p2383) ∨ p2619 ∨ p3156 ∨ p3609 ∨ (¬ p5017) ∨ (¬ p2088) ∨ (¬ p2870) ∨ (¬ p2190) ∨ p2992 ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5017 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p4114) := (Or.elim h112008 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u8 q8))) (fun r8 => (False.elim (u9 r8))))))))))))))))))));
    (Or.elim h96434 (fun q0 => (False.elim (u10 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114656 (p2088 p2249 p2363 p2383 p2641 p2651 p2911 p2922 p3487 p3567 p4114 p4133 : Prop)
    (h105712 : p4133)
    (h106513 : p2249)
    (h98180 : p2363 ∨ p2922 ∨ p2911 ∨ (¬ p4114) ∨ (¬ p2641) ∨ (¬ p3487) ∨ (¬ p4133) ∨ (¬ p2088) ∨ (¬ p2249) ∨ p2651 ∨ (¬ p3567))
    (h96434 : p4114 ∨ (¬ p2383))
    : (¬ p2383) ∨ p2363 ∨ p2922 ∨ p2911 ∨ (¬ p2641) ∨ (¬ p2088) ∨ (¬ p3567) ∨ (¬ p3487) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4133 := h105712;
    let u10 : p2249 := h106513;
    let u11 : (¬ p4114) := (Or.elim h98180 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u8 q9))) (fun r9 => (False.elim (r9 u6))))))))))))))))))))));
    (Or.elim h96434 (fun q0 => (False.elim (u11 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114663 (p2252 p2363 p2383 p2651 p2745 p2797 p2881 p3201 p3567 p3683 p3998 p4001 p4114 p5580 : Prop)
    (h105523 : p2745)
    (h101488 : (¬ p3998) ∨ (¬ p5580) ∨ p2881 ∨ (¬ p3683) ∨ (¬ p2745) ∨ (¬ p3567) ∨ (¬ p2252) ∨ (¬ p2797) ∨ (¬ p4114) ∨ (¬ p4001) ∨ (¬ p2363) ∨ p3201 ∨ p2651)
    (h96434 : p4114 ∨ (¬ p2383))
    : (¬ p2383) ∨ (¬ p5580) ∨ (¬ p3998) ∨ p2881 ∨ (¬ p2797) ∨ p3201 ∨ (¬ p3567) ∨ (¬ p2363) ∨ p2651 ∨ (¬ p4001) ∨ (¬ p2252) ∨ (¬ p3683) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p2745 := h105523;
    let u13 : (¬ p4114) := (Or.elim h101488 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => q8) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u7))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (u5 q11))) (fun r11 => (False.elim (u8 r11))))))))))))))))))))))))));
    (Or.elim h96434 (fun q0 => (False.elim (u13 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114667 (p2341 p2482 p4590 p5201 : Prop)
    (h22275 : p2482 ∨ (¬ p4590) ∨ (¬ p5201))
    (h96447 : p4590 ∨ (¬ p2341))
    : (¬ p2341) ∨ p2482 ∨ (¬ p5201) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2482) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4590) := (Or.elim h22275 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96447 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114668 (p2341 p4238 p4590 p4988 : Prop)
    (h40137 : p4238 ∨ (¬ p4590) ∨ (¬ p4988))
    (h96447 : p4590 ∨ (¬ p2341))
    : (¬ p2341) ∨ p4238 ∨ (¬ p4988) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4238) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4590) := (Or.elim h40137 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u2))))));
    (Or.elim h96447 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114669 (p2341 p3545 p4590 p5242 : Prop)
    (h25582 : (¬ p3545) ∨ (¬ p4590) ∨ p5242)
    (h96447 : p4590 ∨ (¬ p2341))
    : (¬ p2341) ∨ p5242 ∨ (¬ p3545) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5242) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3545 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4590) := (Or.elim h25582 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h96447 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114672 (p2341 p2717 p3577 p4403 p4590 : Prop)
    (h95778 : (¬ p3577) ∨ (¬ p4590) ∨ (¬ p4403) ∨ p2717)
    (h96447 : p4590 ∨ (¬ p2341))
    : (¬ p2341) ∨ p2717 ∨ (¬ p3577) ∨ (¬ p4403) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4403 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4590) := (Or.elim h95778 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u1 r2))))))));
    (Or.elim h96447 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114673 (p2341 p2911 p3998 p4590 p5203 p5558 : Prop)
    (h105490 : p5203)
    (h89418 : (¬ p3998) ∨ (¬ p5558) ∨ p2911 ∨ (¬ p5203) ∨ (¬ p4590))
    (h96447 : p4590 ∨ (¬ p2341))
    : (¬ p2341) ∨ (¬ p5558) ∨ (¬ p3998) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5203 := h105490;
    let u5 : (¬ p4590) := (Or.elim h89418 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h96447 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114674 (p2088 p2341 p3537 p3609 p3819 p4590 : Prop)
    (h89904 : p3537 ∨ p3609 ∨ (¬ p4590) ∨ (¬ p2088) ∨ (¬ p3819))
    (h96447 : p4590 ∨ (¬ p2341))
    : (¬ p2341) ∨ (¬ p3819) ∨ (¬ p2088) ∨ p3609 ∨ p3537 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4590) := (Or.elim h89904 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h96447 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114676 (p2088 p2341 p2459 p2717 p4590 p5261 : Prop)
    (h95332 : p2717 ∨ (¬ p4590) ∨ p2459 ∨ (¬ p2088) ∨ (¬ p5261))
    (h96447 : p4590 ∨ (¬ p2341))
    : (¬ p2341) ∨ p2459 ∨ (¬ p2088) ∨ (¬ p5261) ∨ p2717 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4590) := (Or.elim h95332 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h96447 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114677 (p2088 p2264 p2341 p2459 p4590 p4854 : Prop)
    (h96664 : (¬ p4590) ∨ p2264 ∨ (¬ p4854) ∨ (¬ p2088) ∨ p2459)
    (h96447 : p4590 ∨ (¬ p2341))
    : (¬ p2341) ∨ p2459 ∨ (¬ p2088) ∨ (¬ p4854) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4854 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4590) := (Or.elim h96664 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h96447 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114679 (p2341 p2396 p3516 p3998 p4590 p5558 : Prop)
    (h101550 : (¬ p3998) ∨ p3516 ∨ (¬ p2396) ∨ (¬ p4590) ∨ (¬ p5558))
    (h96447 : p4590 ∨ (¬ p2341))
    : (¬ p2341) ∨ (¬ p2396) ∨ (¬ p3998) ∨ p3516 ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4590) := (Or.elim h101550 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96447 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114681 (p2088 p2341 p2459 p4066 p4391 p4590 p5559 : Prop)
    (h106189 : p5559)
    (h74612 : (¬ p4066) ∨ (¬ p4391) ∨ (¬ p5559) ∨ (¬ p4590) ∨ p2459 ∨ (¬ p2088))
    (h96447 : p4590 ∨ (¬ p2341))
    : (¬ p2341) ∨ (¬ p4391) ∨ (¬ p2088) ∨ p2459 ∨ (¬ p4066) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5559 := h106189;
    let u6 : (¬ p4590) := (Or.elim h74612 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h96447 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114684 (p2088 p2341 p2459 p2707 p2737 p3577 p4590 : Prop)
    (h81306 : (¬ p3577) ∨ (¬ p4590) ∨ (¬ p2707) ∨ p2737 ∨ p2459 ∨ (¬ p2088))
    (h96447 : p4590 ∨ (¬ p2341))
    : (¬ p2341) ∨ (¬ p2088) ∨ (¬ p3577) ∨ (¬ p2707) ∨ p2459 ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4590) := (Or.elim h81306 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h96447 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114687 (p2088 p2341 p2427 p3073 p3691 p4492 p4590 : Prop)
    (h107422 : p3073 ∨ (¬ p3691) ∨ (¬ p4492) ∨ (¬ p4590) ∨ (¬ p2427) ∨ (¬ p2088))
    (h96447 : p4590 ∨ (¬ p2341))
    : (¬ p2341) ∨ (¬ p4492) ∨ (¬ p2088) ∨ (¬ p2427) ∨ p3073 ∨ (¬ p3691) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4492 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4590) := (Or.elim h107422 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h96447 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114689 (p2088 p2255 p2341 p3189 p3256 p4104 p4590 : Prop)
    (h105367 : p2255)
    (h100549 : p3189 ∨ p3256 ∨ (¬ p4590) ∨ (¬ p2088) ∨ (¬ p4104) ∨ (¬ p2255))
    (h96447 : p4590 ∨ (¬ p2341))
    : (¬ p2341) ∨ p3189 ∨ p3256 ∨ (¬ p2088) ∨ (¬ p4104) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2255 := h105367;
    let u6 : (¬ p4590) := (Or.elim h100549 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96447 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114702 (p2088 p2341 p2751 p2996 p3609 p4066 p4364 p4590 : Prop)
    (h106343 : p2751)
    (h82146 : p3609 ∨ (¬ p4590) ∨ (¬ p2751) ∨ (¬ p2088) ∨ p2996 ∨ (¬ p4066) ∨ (¬ p4364))
    (h96447 : p4590 ∨ (¬ p2341))
    : (¬ p2341) ∨ (¬ p4364) ∨ (¬ p2088) ∨ p3609 ∨ (¬ p4066) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2751 := h106343;
    let u7 : (¬ p4590) := (Or.elim h82146 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u1))))))))))))));
    (Or.elim h96447 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114703 (p2341 p2417 p2619 p3516 p3741 p4115 p4590 p4882 : Prop)
    (h105453 : p4882)
    (h84795 : p3516 ∨ (¬ p2417) ∨ (¬ p4882) ∨ (¬ p3741) ∨ (¬ p4115) ∨ p2619 ∨ (¬ p4590))
    (h96447 : p4590 ∨ (¬ p2341))
    : (¬ p2341) ∨ p2619 ∨ (¬ p4115) ∨ p3516 ∨ (¬ p3741) ∨ (¬ p2417) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4882 := h105453;
    let u7 : (¬ p4590) := (Or.elim h84795 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u1 q5))) (fun r5 => r5))))))))))));
    (Or.elim h96447 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114705 (p2088 p2274 p2312 p2341 p3073 p4371 p4514 p4590 : Prop)
    (h87556 : p3073 ∨ (¬ p4590) ∨ (¬ p4514) ∨ (¬ p4371) ∨ (¬ p2312) ∨ (¬ p2088) ∨ (¬ p2274))
    (h96447 : p4590 ∨ (¬ p2341))
    : (¬ p2341) ∨ (¬ p4371) ∨ p3073 ∨ (¬ p2274) ∨ (¬ p2312) ∨ (¬ p2088) ∨ (¬ p4514) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4590) := (Or.elim h87556 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u3))))))))))))));
    (Or.elim h96447 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114709 (p2088 p2295 p2312 p2341 p3073 p4371 p4590 p4757 : Prop)
    (h91826 : p3073 ∨ (¬ p4590) ∨ (¬ p4371) ∨ (¬ p4757) ∨ (¬ p2295) ∨ (¬ p2312) ∨ (¬ p2088))
    (h96447 : p4590 ∨ (¬ p2341))
    : (¬ p2341) ∨ p3073 ∨ (¬ p2088) ∨ (¬ p4757) ∨ (¬ p2312) ∨ (¬ p4371) ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4757 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4590) := (Or.elim h91826 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u2))))))))))))));
    (Or.elim h96447 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114713 (p2088 p2341 p2727 p3073 p3189 p4066 p4590 p4650 : Prop)
    (h110251 : p3189 ∨ (¬ p2088) ∨ p3073 ∨ (¬ p4066) ∨ (¬ p4590) ∨ (¬ p2727) ∨ (¬ p4650))
    (h96447 : p4590 ∨ (¬ p2341))
    : (¬ p2341) ∨ p3189 ∨ (¬ p2088) ∨ p3073 ∨ (¬ p4066) ∨ (¬ p2727) ∨ (¬ p4650) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4590) := (Or.elim h110251 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u6))))))))))))));
    (Or.elim h96447 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114715 (p2088 p2341 p2951 p3073 p3136 p3189 p4590 p4988 : Prop)
    (h110257 : p3189 ∨ (¬ p2088) ∨ p3073 ∨ (¬ p2951) ∨ (¬ p4988) ∨ (¬ p4590) ∨ (¬ p3136))
    (h96447 : p4590 ∨ (¬ p2341))
    : (¬ p2341) ∨ p3189 ∨ (¬ p2088) ∨ p3073 ∨ (¬ p2951) ∨ (¬ p4988) ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4590) := (Or.elim h110257 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (r5 u6))))))))))))));
    (Or.elim h96447 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114731 (p2088 p2341 p2427 p2493 p2619 p2860 p3379 p3609 p3660 p4590 : Prop)
    (h112009 : p2619 ∨ (¬ p4590) ∨ p3609 ∨ p2493 ∨ p3379 ∨ (¬ p2860) ∨ (¬ p2088) ∨ (¬ p3660) ∨ p2427)
    (h96447 : p4590 ∨ (¬ p2341))
    : (¬ p2341) ∨ p2619 ∨ p3609 ∨ p2493 ∨ p3379 ∨ (¬ p2860) ∨ (¬ p2088) ∨ (¬ p3660) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p4590) := (Or.elim h112009 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (u8 r7))))))))))))))))));
    (Or.elim h96447 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114743 (p2774 p2779 p3483 p3654 : Prop)
    (h6560 : (¬ p2779) ∨ p3483 ∨ (¬ p3654))
    (h96911 : p2779 ∨ p2774)
    : p2774 ∨ (¬ p3654) ∨ p3483 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3483) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2779) := (Or.elim h6560 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u1))))));
    (Or.elim h96911 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114744 (p2383 p2774 p2779 p2819 : Prop)
    (h95713 : (¬ p2383) ∨ (¬ p2779) ∨ p2819)
    (h96911 : p2779 ∨ p2774)
    : p2774 ∨ p2819 ∨ (¬ p2383) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2779) := (Or.elim h95713 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h96911 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114745 (p2386 p2774 p2779 p4390 : Prop)
    (h21431 : (¬ p2386) ∨ (¬ p2779) ∨ p4390)
    (h96911 : p2779 ∨ p2774)
    : p2774 ∨ p4390 ∨ (¬ p2386) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4390) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2779) := (Or.elim h21431 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h96911 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114746 (p2122 p2307 p2774 p2779 : Prop)
    (h95727 : (¬ p2779) ∨ (¬ p2307) ∨ p2122)
    (h96911 : p2779 ∨ p2774)
    : p2774 ∨ (¬ p2307) ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2779) := (Or.elim h95727 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h96911 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114747 (p2307 p2774 p2779 p2819 p3325 : Prop)
    (h95718 : (¬ p3325) ∨ (¬ p2307) ∨ (¬ p2779) ∨ p2819)
    (h96911 : p2779 ∨ p2774)
    : p2774 ∨ (¬ p3325) ∨ (¬ p2307) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2779) := (Or.elim h95718 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (u3 r2))))))));
    (Or.elim h96911 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114753 (p2177 p2307 p2737 p2774 p2779 p2829 : Prop)
    (h81293 : (¬ p2779) ∨ (¬ p2829) ∨ (¬ p2177) ∨ (¬ p2307) ∨ p2737)
    (h96911 : p2779 ∨ p2774)
    : p2774 ∨ (¬ p2829) ∨ (¬ p2177) ∨ p2737 ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2779) := (Or.elim h81293 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h96911 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114759 (p2737 p2774 p2779 p2829 p3461 p3654 : Prop)
    (h95711 : (¬ p2779) ∨ p2737 ∨ (¬ p2829) ∨ (¬ p3654) ∨ (¬ p3461))
    (h96911 : p2779 ∨ p2774)
    : p2774 ∨ (¬ p3461) ∨ (¬ p3654) ∨ p2737 ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2779) := (Or.elim h95711 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1))))))))));
    (Or.elim h96911 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114760 (p2307 p2553 p2774 p2779 p2829 p3367 : Prop)
    (h95719 : (¬ p2779) ∨ (¬ p2829) ∨ p2553 ∨ (¬ p2307) ∨ p3367)
    (h96911 : p2779 ∨ p2774)
    : p2774 ∨ (¬ p2307) ∨ p2553 ∨ p3367 ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2779) := (Or.elim h95719 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u3 r3))))))))));
    (Or.elim h96911 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114764 (p2307 p2396 p2761 p2774 p2779 p2829 : Prop)
    (h46120 : (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p2779) ∨ (¬ p2829))
    (h96911 : p2779 ∨ p2774)
    : p2774 ∨ (¬ p2761) ∨ (¬ p2396) ∨ (¬ p2829) ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2779) := (Or.elim h46120 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h96911 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114765 (p2122 p2383 p2774 p2779 p3979 p5558 : Prop)
    (h97902 : (¬ p5558) ∨ p2122 ∨ (¬ p3979) ∨ (¬ p2779) ∨ (¬ p2383))
    (h96911 : p2779 ∨ p2774)
    : p2774 ∨ (¬ p3979) ∨ (¬ p2383) ∨ p2122 ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2779) := (Or.elim h97902 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u2))))))))));
    (Or.elim h96911 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114766 (p2363 p2383 p2774 p2779 p2829 p2839 : Prop)
    (h101494 : (¬ p2829) ∨ (¬ p2779) ∨ p2839 ∨ (¬ p2383) ∨ (¬ p2363))
    (h96911 : p2779 ∨ p2774)
    : p2774 ∨ (¬ p2383) ∨ (¬ p2829) ∨ p2839 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2779) := (Or.elim h101494 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h96911 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114767 (p2363 p2383 p2774 p2779 p3917 p3979 : Prop)
    (h111684 : p2363 ∨ (¬ p3979) ∨ (¬ p3917) ∨ (¬ p2383) ∨ (¬ p2779))
    (h96911 : p2779 ∨ p2774)
    : p2774 ∨ p2363 ∨ (¬ p3979) ∨ (¬ p3917) ∨ (¬ p2383) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2779) := (Or.elim h111684 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => r3))))))));
    (Or.elim h96911 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114770 (p2177 p2319 p2396 p2774 p2779 p2829 p3516 : Prop)
    (h86910 : p2396 ∨ (¬ p3516) ∨ (¬ p2319) ∨ (¬ p2829) ∨ (¬ p2177) ∨ (¬ p2779))
    (h96911 : p2779 ∨ p2774)
    : p2774 ∨ (¬ p3516) ∨ (¬ p2319) ∨ (¬ p2829) ∨ p2396 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2779) := (Or.elim h86910 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h96911 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114773 (p2563 p2774 p2779 p2829 p2839 p4356 p4885 : Prop)
    (h95700 : (¬ p2829) ∨ (¬ p4356) ∨ p2563 ∨ p2839 ∨ (¬ p2779) ∨ (¬ p4885))
    (h96911 : p2779 ∨ p2774)
    : p2774 ∨ p2563 ∨ (¬ p4356) ∨ p2839 ∨ (¬ p2829) ∨ (¬ p4885) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2779) := (Or.elim h95700 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h96911 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114774 (p2383 p2737 p2774 p2779 p3923 p3953 p4842 : Prop)
    (h42325 : (¬ p2383) ∨ (¬ p2737) ∨ (¬ p2779) ∨ (¬ p3923) ∨ (¬ p3953) ∨ (¬ p4842))
    (h96911 : p2779 ∨ p2774)
    : p2774 ∨ (¬ p3923) ∨ (¬ p4842) ∨ (¬ p2383) ∨ (¬ p3953) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2779) := (Or.elim h42325 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h96911 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114775 (p2307 p2737 p2774 p2779 p3309 p3953 p4842 : Prop)
    (h95707 : (¬ p2779) ∨ (¬ p3953) ∨ p3309 ∨ (¬ p4842) ∨ (¬ p2737) ∨ (¬ p2307))
    (h96911 : p2779 ∨ p2774)
    : p2774 ∨ (¬ p3953) ∨ (¬ p2307) ∨ (¬ p4842) ∨ (¬ p2737) ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p3953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2779) := (Or.elim h95707 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h96911 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114781 (p2177 p2386 p2553 p2774 p2779 p2829 p3367 : Prop)
    (h95729 : (¬ p2779) ∨ (¬ p2829) ∨ (¬ p2177) ∨ (¬ p2386) ∨ (¬ p2553) ∨ p3367)
    (h96911 : p2779 ∨ p2774)
    : p2774 ∨ (¬ p2829) ∨ p3367 ∨ (¬ p2553) ∨ (¬ p2386) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2779) := (Or.elim h95729 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u2 r4))))))))))));
    (Or.elim h96911 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114783 (p2386 p2437 p2774 p2779 p2819 p3016 p4710 : Prop)
    (h98082 : (¬ p4710) ∨ (¬ p2779) ∨ p2819 ∨ p3016 ∨ (¬ p2386) ∨ (¬ p2437))
    (h96911 : p2779 ∨ p2774)
    : p2774 ∨ (¬ p2437) ∨ (¬ p2386) ∨ p2819 ∨ (¬ p4710) ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2779) := (Or.elim h98082 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h96911 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114804 (p2177 p2307 p2696 p2727 p2748 p2774 p2779 p2829 p3083 : Prop)
    (h107583 : (¬ p2779) ∨ (¬ p2829) ∨ p3083 ∨ (¬ p2748) ∨ (¬ p2307) ∨ p2696 ∨ (¬ p2177) ∨ p2727)
    (h96911 : p2779 ∨ p2774)
    : p2774 ∨ (¬ p2829) ∨ (¬ p2177) ∨ (¬ p2307) ∨ p2696 ∨ p3083 ∨ (¬ p2748) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2779) := (Or.elim h107583 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u4 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (u7 r6))))))))))))))));
    (Or.elim h96911 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114807 (p2307 p2396 p2406 p2598 p2774 p2779 p2829 p2982 p3951 p4030 : Prop)
    (h106536 : p3951)
    (h81118 : (¬ p2829) ∨ (¬ p2307) ∨ p2598 ∨ (¬ p3951) ∨ (¬ p2779) ∨ (¬ p2396) ∨ p2982 ∨ p2406 ∨ (¬ p4030))
    (h96911 : p2779 ∨ p2774)
    : p2774 ∨ (¬ p2829) ∨ (¬ p2307) ∨ (¬ p2396) ∨ p2406 ∨ p2598 ∨ p2982 ∨ (¬ p4030) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3951 := h106536;
    let u9 : (¬ p2779) := (Or.elim h81118 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u6 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u4 q7))) (fun r7 => (False.elim (r7 u7))))))))))))))))));
    (Or.elim h96911 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114808 (p2307 p2396 p2696 p2748 p2774 p2779 p2829 p3189 p3256 p3950 : Prop)
    (h82717 : (¬ p2396) ∨ (¬ p2307) ∨ p3256 ∨ (¬ p2748) ∨ (¬ p2829) ∨ (¬ p2779) ∨ p2696 ∨ p3189 ∨ (¬ p3950))
    (h96911 : p2779 ∨ p2774)
    : p2774 ∨ p3256 ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p3950) ∨ p2696 ∨ (¬ p2748) ∨ (¬ p2829) ∨ p3189 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2779) := (Or.elim h82717 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u5 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u8 q7))) (fun r7 => (False.elim (r7 u4))))))))))))))))));
    (Or.elim h96911 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114810 (p2274 p2307 p2598 p2696 p2774 p2779 p2860 p3125 p3564 p5160 : Prop)
    (h113540 : (¬ p2860) ∨ (¬ p3564) ∨ (¬ p2696) ∨ p2274 ∨ p2598 ∨ (¬ p3125) ∨ (¬ p5160) ∨ (¬ p2779) ∨ (¬ p2307))
    (h96911 : p2779 ∨ p2774)
    : p2774 ∨ (¬ p2860) ∨ (¬ p3564) ∨ (¬ p2696) ∨ p2274 ∨ p2598 ∨ (¬ p3125) ∨ (¬ p5160) ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2779) := (Or.elim h113540 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u5 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => q7) (fun r7 => (False.elim (r7 u8))))))))))))))))));
    (Or.elim h96911 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114811 (p2417 p2598 p2696 p2761 p2774 p2779 p2860 p3461 p3654 p5160 : Prop)
    (h113541 : (¬ p2860) ∨ (¬ p2417) ∨ (¬ p5160) ∨ p2761 ∨ (¬ p3461) ∨ (¬ p3654) ∨ (¬ p2696) ∨ p2598 ∨ (¬ p2779))
    (h96911 : p2779 ∨ p2774)
    : p2774 ∨ (¬ p2860) ∨ (¬ p2417) ∨ (¬ p5160) ∨ p2761 ∨ (¬ p3461) ∨ (¬ p3654) ∨ (¬ p2696) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2779) := (Or.elim h113541 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u8 q7))) (fun r7 => r7))))))))))))))));
    (Or.elim h96911 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114813 (p2088 p2363 p2383 p2696 p2748 p2774 p2779 p2829 p2992 p3156 : Prop)
    (h114650 : (¬ p2383) ∨ (¬ p2088) ∨ p2992 ∨ (¬ p2779) ∨ p2363 ∨ (¬ p2829) ∨ (¬ p2748) ∨ p3156 ∨ p2696)
    (h96911 : p2779 ∨ p2774)
    : p2774 ∨ (¬ p2383) ∨ (¬ p2088) ∨ p2992 ∨ p2363 ∨ (¬ p2829) ∨ (¬ p2748) ∨ p3156 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2779) := (Or.elim h114650 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u7 q7))) (fun r7 => (False.elim (u8 r7))))))))))))))))));
    (Or.elim h96911 (fun q0 => (False.elim (u9 q0))) (fun r0 => (False.elim (u0 r0)))))

theorem step114823 (p2088 p2363 p2383 p3322 : Prop)
    (h112711 : p2383 ∨ p2363 ∨ (¬ p3322) ∨ (¬ p2088))
    (h96437 : p3322 ∨ p2363)
    : p2383 ∨ p2363 ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2383) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3322) := (Or.elim h112711 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u2))))))));
    (Or.elim h96437 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (u1 r0)))))

theorem step114825 (p2440 p2727 p2992 p4700 : Prop)
    (h81805 : (¬ p2992) ∨ p2727 ∨ (¬ p4700))
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ (¬ p2992) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4700) := (Or.elim h81805 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h100363 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114826 (p2440 p2651 p2946 p4700 : Prop)
    (h83037 : (¬ p2946) ∨ p2651 ∨ (¬ p4700))
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ (¬ p2946) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4700) := (Or.elim h83037 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => r1))));
    (Or.elim h100363 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114828 (p2440 p3661 p3878 p4700 : Prop)
    (h32126 : (¬ p3661) ∨ p3878 ∨ (¬ p4700))
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ p3878 ∨ (¬ p3661) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3878) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4700) := (Or.elim h32126 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => r1))));
    (Or.elim h100363 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114829 (p2440 p2630 p3136 p4700 : Prop)
    (h84307 : (¬ p3136) ∨ (¬ p4700) ∨ p2630)
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ (¬ p3136) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4700) := (Or.elim h84307 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    (Or.elim h100363 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114831 (p2440 p4700 p5008 p5062 : Prop)
    (h105469 : p5008)
    (h31515 : (¬ p4700) ∨ (¬ p5008) ∨ p5062)
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ p5062 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5062) := (fun h => hn (Or.inr h));
    let u2 : p5008 := h105469;
    let u3 : (¬ p4700) := (Or.elim h31515 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1))))));
    (Or.elim h100363 (fun q0 => (False.elim (u3 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114836 (p2440 p3016 p4700 p5740 p6116 : Prop)
    (h110778 : p6116 ∨ (¬ p5740) ∨ (¬ p4700) ∨ (¬ p3016))
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ p6116 ∨ (¬ p5740) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p6116) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4700) := (Or.elim h110778 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u3))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u4 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114841 (p2373 p2440 p2850 p3156 p4700 p4753 : Prop)
    (h105514 : p4753)
    (h79139 : (¬ p4700) ∨ p3156 ∨ (¬ p2850) ∨ (¬ p2373) ∨ (¬ p4753))
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ p3156 ∨ (¬ p2373) ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4753 := h105514;
    let u5 : (¬ p4700) := (Or.elim h79139 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114842 (p2284 p2440 p2553 p3125 p3564 p4700 : Prop)
    (h79507 : (¬ p3564) ∨ p3125 ∨ p2553 ∨ p2284 ∨ (¬ p4700))
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ (¬ p3564) ∨ p2284 ∨ p3125 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4700) := (Or.elim h79507 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => r3))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114843 (p2241 p2284 p2440 p2563 p2727 p4700 : Prop)
    (h80838 : p2241 ∨ p2284 ∨ (¬ p2563) ∨ p2727 ∨ (¬ p4700))
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ p2284 ∨ p2241 ∨ (¬ p2563) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4700) := (Or.elim h80838 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => r3))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114845 (p2427 p2440 p2563 p2727 p2901 p4700 : Prop)
    (h83044 : p2727 ∨ p2901 ∨ (¬ p2427) ∨ (¬ p4700) ∨ p2563)
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ p2563 ∨ p2727 ∨ (¬ p2427) ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4700) := (Or.elim h83044 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114846 (p2284 p2437 p2440 p2563 p4646 p4700 : Prop)
    (h105534 : p4646)
    (h83046 : p2284 ∨ (¬ p2437) ∨ (¬ p2563) ∨ (¬ p4700) ∨ (¬ p4646))
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ p2284 ∨ (¬ p2437) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4646 := h105534;
    let u5 : (¬ p4700) := (Or.elim h83046 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114847 (p2373 p2440 p3016 p3156 p4700 p4717 : Prop)
    (h105424 : p4717)
    (h83047 : p3156 ∨ (¬ p3016) ∨ (¬ p4717) ∨ (¬ p2373) ∨ (¬ p4700))
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ p3156 ∨ (¬ p2373) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4717 := h105424;
    let u5 : (¬ p4700) := (Or.elim h83047 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => r3))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114848 (p2284 p2440 p2563 p3343 p4700 p4953 : Prop)
    (h83052 : (¬ p3343) ∨ p2284 ∨ (¬ p4700) ∨ (¬ p4953) ∨ (¬ p2563))
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ p2284 ∨ (¬ p3343) ∨ (¬ p2563) ∨ (¬ p4953) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4700) := (Or.elim h83052 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114849 (p2440 p2641 p2972 p3115 p4365 p4700 : Prop)
    (h107266 : p3115 ∨ (¬ p4365) ∨ (¬ p2972) ∨ (¬ p4700) ∨ p2641)
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ (¬ p4365) ∨ p3115 ∨ (¬ p2972) ∨ p2641 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4700) := (Or.elim h107266 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u4 r3))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114850 (p2331 p2440 p2901 p2958 p3051 p4700 : Prop)
    (h107328 : p2901 ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p4700) ∨ p2331)
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ (¬ p3051) ∨ p2331 ∨ p2901 ∨ (¬ p2958) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4700) := (Or.elim h107328 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114851 (p2220 p2331 p2440 p2958 p3156 p4700 : Prop)
    (h107330 : p3156 ∨ (¬ p2220) ∨ (¬ p2958) ∨ (¬ p4700) ∨ p2331)
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ p3156 ∨ p2331 ∨ (¬ p2220) ∨ (¬ p2958) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4700) := (Or.elim h107330 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114854 (p2284 p2440 p2509 p2563 p3083 p4700 : Prop)
    (h98823 : (¬ p2509) ∨ (¬ p3083) ∨ (¬ p4700) ∨ (¬ p2563) ∨ p2284)
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ p2284 ∨ (¬ p2509) ∨ (¬ p3083) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4700) := (Or.elim h98823 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u1 r3))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114855 (p2440 p2619 p2797 p3156 p4313 p4700 : Prop)
    (h107359 : (¬ p4313) ∨ p2797 ∨ (¬ p2619) ∨ (¬ p4700) ∨ p3156)
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ (¬ p2619) ∨ p3156 ∨ (¬ p4313) ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4700) := (Or.elim h107359 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u2 r3))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114857 (p2440 p3422 p3888 p4153 p4228 p4700 : Prop)
    (h110225 : p4228 ∨ (¬ p3888) ∨ (¬ p4153) ∨ (¬ p4700) ∨ (¬ p3422))
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ p4228 ∨ (¬ p3888) ∨ (¬ p4153) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4228) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3888 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p4700) := (Or.elim h110225 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u4))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u5 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114861 (p2440 p2727 p2745 p2870 p2901 p4313 p4700 : Prop)
    (h105523 : p2745)
    (h82523 : p2901 ∨ (¬ p2870) ∨ (¬ p2745) ∨ (¬ p4700) ∨ (¬ p4313) ∨ p2727)
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ p2901 ∨ p2727 ∨ (¬ p4313) ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2745 := h105523;
    let u6 : (¬ p4700) := (Or.elim h82523 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u2 r4))))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114866 (p2156 p2284 p2406 p2440 p4109 p4700 p4814 : Prop)
    (h105440 : p4814)
    (h83054 : (¬ p2156) ∨ (¬ p2406) ∨ p2284 ∨ (¬ p4109) ∨ (¬ p4814) ∨ (¬ p4700))
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ (¬ p2156) ∨ p2284 ∨ (¬ p4109) ∨ (¬ p2406) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4814 := h105440;
    let u6 : (¬ p4700) := (Or.elim h83054 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => r4))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114867 (p2156 p2284 p2440 p2850 p4109 p4700 p4753 : Prop)
    (h105514 : p4753)
    (h83056 : p2284 ∨ (¬ p4753) ∨ (¬ p4700) ∨ (¬ p4109) ∨ (¬ p2156) ∨ (¬ p2850))
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ p2284 ∨ (¬ p2156) ∨ (¬ p2850) ∨ (¬ p4109) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4753 := h105514;
    let u6 : (¬ p4700) := (Or.elim h83056 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114868 (p2406 p2440 p2901 p3051 p4109 p4700 p4814 : Prop)
    (h105440 : p4814)
    (h83062 : (¬ p3051) ∨ p2901 ∨ (¬ p4109) ∨ (¬ p4700) ∨ (¬ p2406) ∨ (¬ p4814))
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ (¬ p3051) ∨ p2901 ∨ (¬ p4109) ∨ (¬ p2406) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4814 := h105440;
    let u6 : (¬ p4700) := (Or.elim h83062 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114870 (p2440 p2850 p2901 p3051 p4109 p4700 p4753 : Prop)
    (h105514 : p4753)
    (h83066 : p2901 ∨ (¬ p2850) ∨ (¬ p3051) ∨ (¬ p4753) ∨ (¬ p4109) ∨ (¬ p4700))
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ (¬ p3051) ∨ (¬ p4109) ∨ p2901 ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4753 := h105514;
    let u6 : (¬ p4700) := (Or.elim h83066 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => r4))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114872 (p2440 p2797 p2870 p2957 p3051 p4313 p4700 : Prop)
    (h107398 : (¬ p4313) ∨ p2797 ∨ (¬ p2957) ∨ (¬ p2870) ∨ (¬ p4700) ∨ p3051)
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ (¬ p4313) ∨ (¬ p2957) ∨ p3051 ∨ (¬ p2870) ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4700) := (Or.elim h107398 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (u3 r4))))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114873 (p2440 p2727 p2745 p3105 p3115 p4313 p4700 : Prop)
    (h105523 : p2745)
    (h87195 : (¬ p3105) ∨ p2727 ∨ (¬ p2745) ∨ (¬ p4700) ∨ p3115 ∨ (¬ p4313))
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ p3115 ∨ (¬ p4313) ∨ p2727 ∨ (¬ p3105) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2745 := h105523;
    let u6 : (¬ p4700) := (Or.elim h87195 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (False.elim (r4 u2))))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114875 (p2427 p2440 p2850 p2957 p3051 p4700 p4753 : Prop)
    (h105514 : p4753)
    (h87770 : (¬ p2850) ∨ p3051 ∨ (¬ p4753) ∨ (¬ p2957) ∨ (¬ p2427) ∨ (¬ p4700))
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ (¬ p2957) ∨ p3051 ∨ (¬ p2427) ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4753 := h105514;
    let u6 : (¬ p4700) := (Or.elim h87770 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => r4))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114877 (p2166 p2241 p2440 p3016 p3156 p4365 p4700 : Prop)
    (h92344 : (¬ p4365) ∨ p3156 ∨ (¬ p4700) ∨ (¬ p3016) ∨ (¬ p2241) ∨ (¬ p2166))
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ (¬ p2166) ∨ (¬ p4365) ∨ p3156 ∨ (¬ p3016) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4700) := (Or.elim h92344 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1))))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114879 (p2156 p2220 p2284 p2363 p2440 p4506 p4700 : Prop)
    (h92465 : p2363 ∨ p2284 ∨ p2220 ∨ (¬ p4506) ∨ (¬ p2156) ∨ (¬ p4700))
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ p2220 ∨ (¬ p2156) ∨ (¬ p4506) ∨ p2284 ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4700) := (Or.elim h92465 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => r4))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114883 (p2440 p2901 p3016 p3051 p4109 p4700 p4717 : Prop)
    (h105424 : p4717)
    (h98215 : p2901 ∨ (¬ p3051) ∨ (¬ p4109) ∨ (¬ p4700) ∨ (¬ p4717) ∨ (¬ p3016))
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ (¬ p3051) ∨ p2901 ∨ (¬ p3016) ∨ (¬ p4109) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4717 := h105424;
    let u6 : (¬ p4700) := (Or.elim h98215 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3))))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114886 (p2440 p2563 p2651 p4236 p4700 p5740 p6116 : Prop)
    (h110782 : p6116 ∨ (¬ p5740) ∨ (¬ p4236) ∨ (¬ p4700) ∨ p2651 ∨ p2563)
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ p6116 ∨ (¬ p5740) ∨ (¬ p4236) ∨ p2651 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p6116) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4700) := (Or.elim h110782 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (u5 r4))))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114887 (p2440 p2685 p2737 p2839 p3136 p4650 p4700 : Prop)
    (h112623 : (¬ p3136) ∨ (¬ p4700) ∨ (¬ p2839) ∨ p2737 ∨ p2685 ∨ (¬ p4650))
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ (¬ p3136) ∨ (¬ p2839) ∨ p2737 ∨ p2685 ∨ (¬ p4650) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4700) := (Or.elim h112623 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114888 (p2132 p2440 p2696 p2797 p3136 p4700 p4972 : Prop)
    (h112629 : (¬ p3136) ∨ (¬ p2132) ∨ p2797 ∨ (¬ p4700) ∨ p2696 ∨ (¬ p4972))
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ (¬ p3136) ∨ (¬ p2132) ∨ p2797 ∨ p2696 ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p4700) := (Or.elim h112629 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u4 q4))) (fun r4 => (False.elim (r4 u5))))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u6 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114893 (p2137 p2440 p2901 p3051 p3083 p3698 p4610 p4700 : Prop)
    (h90176 : (¬ p2137) ∨ p2901 ∨ (¬ p3083) ∨ (¬ p3698) ∨ (¬ p4610) ∨ (¬ p4700) ∨ (¬ p3051))
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ (¬ p3051) ∨ p2901 ∨ (¬ p3083) ∨ (¬ p4610) ∨ (¬ p2137) ∨ (¬ p3698) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4610 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p4700) := (Or.elim h90176 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (False.elim (r5 u1))))))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114896 (p2440 p2578 p2901 p3051 p3422 p4198 p4700 p4753 : Prop)
    (h105514 : p4753)
    (h98219 : (¬ p2578) ∨ p2901 ∨ (¬ p3422) ∨ (¬ p4753) ∨ (¬ p3051) ∨ (¬ p4198) ∨ (¬ p4700))
    (h100363 : p4700 ∨ (¬ p2440))
    : (¬ p2440) ∨ (¬ p4198) ∨ (¬ p2578) ∨ (¬ p3422) ∨ (¬ p3051) ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4753 := h105514;
    let u7 : (¬ p4700) := (Or.elim h98219 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => r5))))))))))));
    (Or.elim h100363 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114906 (p2493 p2761 p3051 p3246 p3379 p3461 p5254 p5514 : Prop)
    (h107504 : (¬ p5514) ∨ (¬ p5254) ∨ (¬ p3246) ∨ (¬ p2761) ∨ p2493 ∨ (¬ p3051) ∨ p3379)
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ (¬ p3246) ∨ (¬ p2761) ∨ p2493 ∨ p3379 ∨ (¬ p3051) ∨ (¬ p5514) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p5254) := (Or.elim h107504 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u3 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (u4 r5))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114907 (p2241 p2641 p2761 p3425 p3434 p3461 p4228 p5254 : Prop)
    (h110230 : p4228 ∨ (¬ p2761) ∨ p2641 ∨ p3425 ∨ (¬ p3434) ∨ p2241 ∨ (¬ p5254))
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ p4228 ∨ (¬ p2761) ∨ p2641 ∨ p3425 ∨ (¬ p3434) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4228) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p5254) := (Or.elim h110230 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => r5))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u7 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114908 (p2254 p2284 p2946 p3193 p3276 p3379 p3461 p4393 p5254 : Prop)
    (h105366 : p2254)
    (h81648 : (¬ p4393) ∨ p3193 ∨ (¬ p2254) ∨ (¬ p3379) ∨ (¬ p3276) ∨ p2284 ∨ p2946 ∨ (¬ p5254))
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ p3193 ∨ (¬ p3276) ∨ (¬ p3379) ∨ p2946 ∨ p2284 ∨ (¬ p4393) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3193) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2254 := h105366;
    let u8 : (¬ p5254) := (Or.elim h81648 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u5 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => r6))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114909 (p2132 p2761 p2860 p3399 p3461 p3631 p4393 p4736 p5254 : Prop)
    (h105431 : p4736)
    (h83261 : (¬ p4393) ∨ p2132 ∨ p2860 ∨ (¬ p3399) ∨ (¬ p4736) ∨ (¬ p2761) ∨ (¬ p5254) ∨ (¬ p3631))
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ (¬ p3399) ∨ (¬ p2761) ∨ p2860 ∨ (¬ p3631) ∨ (¬ p4393) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4736 := h105431;
    let u8 : (¬ p5254) := (Or.elim h83261 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (False.elim (r6 u4))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114911 (p2248 p2449 p2608 p2761 p2807 p2829 p3461 p4329 p5254 : Prop)
    (h105365 : p2248)
    (h90502 : (¬ p4329) ∨ (¬ p2449) ∨ (¬ p2248) ∨ (¬ p2761) ∨ p2608 ∨ (¬ p5254) ∨ p2829 ∨ (¬ p2807))
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ (¬ p4329) ∨ (¬ p2449) ∨ (¬ p2761) ∨ p2829 ∨ (¬ p2807) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4329 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2248 := h105365;
    let u8 : (¬ p5254) := (Or.elim h90502 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u4 q6))) (fun r6 => (False.elim (r6 u5))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114913 (p2248 p2493 p3166 p3256 p3266 p3379 p3461 p5254 p5514 : Prop)
    (h105365 : p2248)
    (h94706 : p3379 ∨ (¬ p5514) ∨ (¬ p3166) ∨ p2493 ∨ (¬ p3266) ∨ (¬ p2248) ∨ (¬ p5254) ∨ (¬ p3256))
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ (¬ p3256) ∨ (¬ p3266) ∨ p2493 ∨ p3379 ∨ (¬ p3166) ∨ (¬ p5514) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2248 := h105365;
    let u8 : (¬ p5254) := (Or.elim h94706 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => q6) (fun r6 => (False.elim (r6 u1))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114914 (p2248 p2449 p2493 p2761 p2807 p3379 p3461 p5254 p5514 : Prop)
    (h105365 : p2248)
    (h94708 : (¬ p5514) ∨ p3379 ∨ (¬ p2807) ∨ (¬ p2761) ∨ p2493 ∨ (¬ p2248) ∨ (¬ p2449) ∨ (¬ p5254))
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ (¬ p5514) ∨ (¬ p2449) ∨ (¬ p2807) ∨ p3379 ∨ (¬ p2761) ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2248 := h105365;
    let u8 : (¬ p5254) := (Or.elim h94708 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => r6))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114915 (p2284 p2341 p2459 p2946 p3266 p3461 p4393 p4850 p5254 : Prop)
    (h94710 : (¬ p4393) ∨ (¬ p3266) ∨ (¬ p4850) ∨ (¬ p2459) ∨ (¬ p2341) ∨ (¬ p5254) ∨ p2284 ∨ p2946)
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ (¬ p4393) ∨ p2284 ∨ (¬ p2341) ∨ p2946 ∨ (¬ p2459) ∨ (¬ p3266) ∨ (¬ p4850) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p5254) := (Or.elim h94710 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => q5) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u2 q6))) (fun r6 => (False.elim (u4 r6))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114916 (p2598 p3166 p3256 p3266 p3422 p3461 p4786 p5254 p5514 : Prop)
    (h106425 : p4786)
    (h94714 : p3422 ∨ (¬ p3166) ∨ (¬ p5514) ∨ (¬ p3266) ∨ (¬ p5254) ∨ p2598 ∨ (¬ p4786) ∨ (¬ p3256))
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ p3422 ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3166) ∨ (¬ p5514) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4786 := h106425;
    let u8 : (¬ p5254) := (Or.elim h94714 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u2))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step114917 (p2132 p2417 p2761 p2860 p3389 p3461 p4393 p4419 p5254 : Prop)
    (h96101 : (¬ p4393) ∨ p2132 ∨ (¬ p5254) ∨ (¬ p2417) ∨ (¬ p4419) ∨ (¬ p2761) ∨ (¬ p3389) ∨ p2860)
    (h102364 : p5254 ∨ (¬ p3461))
    : (¬ p3461) ∨ (¬ p4393) ∨ (¬ p2761) ∨ p2860 ∨ (¬ p2417) ∨ p2132 ∨ (¬ p4419) ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p5254) := (Or.elim h96101 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (u3 r6))))))))))))))));
    (Or.elim h102364 (fun q0 => (False.elim (u8 q0))) (fun r0 => (False.elim (r0 u0)))))

end ElevenRUP
