import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step77372 (p2252 p2459 p2608 p2750 p3166 p3172 p3256 p3379 p3641 p3954 p4030 p4118 p4420 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h73520 : p4118 ∨ p3256)
    (h73498 : p3954 ∨ p2608)
    (h42170 : (¬ p2252) ∨ (¬ p2459) ∨ (¬ p2750) ∨ (¬ p3172) ∨ (¬ p3379) ∨ (¬ p3641) ∨ (¬ p3954) ∨ (¬ p4030) ∨ (¬ p4118) ∨ (¬ p4420))
    : p3166 ∨ p3256 ∨ (¬ p4030) ∨ (¬ p2750) ∨ (¬ p3379) ∨ (¬ p2252) ∨ (¬ p4420) ∨ (¬ p2459) ∨ (¬ p3641) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h42170 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step77373 (p2187 p2274 p2307 p2313 p2608 p3367 p3641 p3989 p4198 p4524 p4596 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73502 : p3989 ∨ p2187)
    (h72962 : p4524)
    (h55548 : (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2608) ∨ (¬ p3367) ∨ (¬ p3641) ∨ (¬ p3989) ∨ (¬ p4198) ∨ (¬ p4524) ∨ (¬ p4596))
    : (¬ p3367) ∨ (¬ p2274) ∨ (¬ p3641) ∨ p2307 ∨ (¬ p2608) ∨ p2187 ∨ (¬ p4198) ∨ (¬ p4596) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p4524 := h72962;
    (Or.elim h55548 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step77375 (p2475 p2930 p3201 p3527 p3548 p3641 p3876 p4403 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73404 : p3548 ∨ p3527)
    (h41094 : (¬ p2475) ∨ (¬ p2930) ∨ (¬ p3548) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p4403))
    : p3201 ∨ (¬ p3641) ∨ (¬ p2930) ∨ (¬ p4403) ∨ (¬ p2475) ∨ p3527 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2930 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4403 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41094 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step77378 (p2253 p2470 p2476 p2946 p2992 p3189 p3201 p3641 p3662 p3876 p4119 p4311 p4647 p5193 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73486 : p3876 ∨ p3201)
    (h73250 : p2476 ∨ p2470)
    (h64093 : (¬ p2253) ∨ (¬ p2476) ∨ (¬ p2946) ∨ (¬ p3189) ∨ (¬ p3641) ∨ (¬ p3662) ∨ (¬ p3876) ∨ (¬ p4119) ∨ (¬ p4311) ∨ (¬ p4647) ∨ (¬ p5193))
    : (¬ p3189) ∨ (¬ p3641) ∨ (¬ p4647) ∨ p2992 ∨ (¬ p4119) ∨ p3201 ∨ (¬ p2946) ∨ (¬ p4311) ∨ (¬ p2253) ∨ (¬ p5193) ∨ p2470 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h64093 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step77379 (p2331 p2363 p2963 p3201 p3256 p3362 p3389 p3641 p3876 p4118 p4196 p4596 p4789 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73338 : p2963 ∨ p2331)
    (h73520 : p4118 ∨ p3256)
    (h65029 : (¬ p2363) ∨ (¬ p2963) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p4118) ∨ (¬ p4196) ∨ (¬ p4596) ∨ (¬ p4789))
    : p3201 ∨ p2331 ∨ p3256 ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p2363) ∨ (¬ p4196) ∨ (¬ p4789) ∨ (¬ p4596) ∨ (¬ p3641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4196 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h65029 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step77384 (p3266 p3276 p3641 p4425 p5160 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h64999 : (¬ p3266) ∨ (¬ p3641) ∨ (¬ p4425) ∨ (¬ p5160))
    : (¬ p5160) ∨ p3276 ∨ (¬ p3641) ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5160 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h64999 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step77388 (p2139 p2156 p2274 p2396 p2470 p2476 p3641 p3905 p4641 p5160 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h48246 : (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2476) ∨ (¬ p3641) ∨ (¬ p3905) ∨ (¬ p4641) ∨ (¬ p5160))
    : (¬ p5160) ∨ (¬ p3641) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2139) ∨ (¬ p3905) ∨ p2470 ∨ (¬ p2156) ∨ (¬ p4641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5160 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h48246 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step77389 (p2192 p2210 p2274 p2470 p2476 p3201 p3641 p3876 p3905 p4712 p4736 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73250 : p2476 ∨ p2470)
    (h52604 : (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2274) ∨ (¬ p2476) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p3905) ∨ (¬ p4712) ∨ (¬ p4736))
    : p3201 ∨ (¬ p3641) ∨ (¬ p2192) ∨ (¬ p3905) ∨ (¬ p4712) ∨ p2470 ∨ (¬ p2210) ∨ (¬ p2274) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h52604 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step77390 (p2230 p2295 p2307 p2313 p2668 p2787 p2850 p3324 p3362 p3641 p3684 p4596 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73386 : p3324 ∨ p2668)
    (h73238 : p2313 ∨ p2307)
    (h65162 : (¬ p2230) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2787) ∨ (¬ p3324) ∨ (¬ p3362) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p4596))
    : p2850 ∨ (¬ p2230) ∨ (¬ p2787) ∨ (¬ p3362) ∨ p2668 ∨ p2307 ∨ (¬ p3641) ∨ (¬ p4596) ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h65162 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step77392 (p2177 p2230 p2295 p2299 p2331 p2850 p2963 p3362 p3568 p3641 p3684 p4420 p4789 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73338 : p2963 ∨ p2331)
    (h73234 : p2299 ∨ p2177)
    (h73442 : p3684 ∨ p2850)
    (h65154 : (¬ p2230) ∨ (¬ p2299) ∨ (¬ p2963) ∨ (¬ p3362) ∨ (¬ p3568) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p4420) ∨ (¬ p4789))
    : (¬ p3641) ∨ p2295 ∨ p2331 ∨ (¬ p4420) ∨ p2177 ∨ (¬ p3362) ∨ p2850 ∨ (¬ p2230) ∨ (¬ p4789) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h65154 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step77394 (p3193 p3222 p3379 p3641 p5160 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h58356 : (¬ p3222) ∨ (¬ p3379) ∨ (¬ p3641) ∨ (¬ p5160))
    : p3193 ∨ (¬ p5160) ∨ (¬ p3379) ∨ (¬ p3641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h58356 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step77396 (p2230 p2241 p2668 p2750 p2850 p3093 p3324 p3519 p3541 p3591 p3641 p3684 p4319 p4596 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73432 : p3591 ∨ p3093)
    (h73386 : p3324 ∨ p2668)
    (h65222 : (¬ p2230) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p3324) ∨ (¬ p3519) ∨ (¬ p3541) ∨ (¬ p3591) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p4319) ∨ (¬ p4596))
    : (¬ p4319) ∨ (¬ p3641) ∨ p2850 ∨ p3093 ∨ (¬ p3541) ∨ (¬ p2750) ∨ (¬ p2241) ∨ (¬ p2230) ∨ p2668 ∨ (¬ p4596) ∨ (¬ p3519) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h65222 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u13))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u0))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step77398 (p2156 p2284 p2753 p3156 p3201 p3362 p3389 p3497 p3641 p3645 p3646 p3876 p4158 p4877 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73436 : p3646 ∨ p2156)
    (h73400 : p3497 ∨ p3156)
    (h65027 : (¬ p2284) ∨ (¬ p2753) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3497) ∨ (¬ p3641) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3876) ∨ (¬ p4158) ∨ (¬ p4877))
    : p3201 ∨ (¬ p2753) ∨ p2156 ∨ (¬ p4158) ∨ p3156 ∨ (¬ p3641) ∨ (¬ p3389) ∨ (¬ p2284) ∨ (¬ p3362) ∨ (¬ p4877) ∨ (¬ p3645) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4158 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u13 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h65027 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u13))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u3))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step77399 (p2573 p2881 p2901 p2946 p2952 p3362 p3422 p3570 p3584 p3641 p4320 p4420 p4789 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h73552 : p4320 ∨ p2901)
    (h73418 : p3570 ∨ p2881)
    (h73330 : p2952 ∨ p2946)
    (h65207 : (¬ p2573) ∨ (¬ p2952) ∨ (¬ p3362) ∨ (¬ p3570) ∨ (¬ p3584) ∨ (¬ p3641) ∨ (¬ p4320) ∨ (¬ p4420) ∨ (¬ p4789))
    : p3422 ∨ (¬ p3641) ∨ (¬ p4789) ∨ p2901 ∨ p2881 ∨ (¬ p2573) ∨ p2946 ∨ (¬ p4420) ∨ (¬ p3362) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h65207 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step77400 (p2187 p2284 p2946 p2952 p3201 p3362 p3389 p3641 p3876 p3952 p3989 p4596 p4789 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73330 : p2952 ∨ p2946)
    (h73502 : p3989 ∨ p2187)
    (h73496 : p3952 ∨ p2284)
    (h64585 : (¬ p2952) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p3952) ∨ (¬ p3989) ∨ (¬ p4596) ∨ (¬ p4789))
    : p3201 ∨ p2946 ∨ (¬ p3389) ∨ (¬ p3362) ∨ (¬ p4789) ∨ p2187 ∨ (¬ p3641) ∨ p2284 ∨ (¬ p4596) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64585 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step77402 (p2156 p2246 p2284 p2470 p2476 p2744 p2901 p2958 p3201 p3366 p3641 p3876 p3905 p3952 p4647 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73496 : p3952 ∨ p2284)
    (h73250 : p2476 ∨ p2470)
    (h52832 : (¬ p2156) ∨ (¬ p2246) ∨ (¬ p2476) ∨ (¬ p2744) ∨ (¬ p2901) ∨ (¬ p2958) ∨ (¬ p3366) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p3905) ∨ (¬ p3952) ∨ (¬ p4647))
    : p3201 ∨ (¬ p3641) ∨ p2284 ∨ (¬ p4647) ∨ p2470 ∨ (¬ p2901) ∨ (¬ p2744) ∨ (¬ p3905) ∨ (¬ p2958) ∨ (¬ p2246) ∨ (¬ p3366) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u13 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u14 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h52832 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u14))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u7))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u13))) (fun r10 => (False.elim (r10 u3)))))))))))))))))))))))))

theorem step77403 (p2509 p2870 p2901 p3054 p3402 p3641 p4244 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h62007 : (¬ p2509) ∨ (¬ p2901) ∨ (¬ p3054) ∨ (¬ p3402) ∨ (¬ p3641) ∨ (¬ p4244))
    : (¬ p2901) ∨ (¬ p3641) ∨ p2870 ∨ (¬ p3402) ∨ (¬ p2509) ∨ (¬ p3054) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3054 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h62007 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step77406 (p2132 p2138 p2598 p3641 p3698 p4610 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h48199 : (¬ p2138) ∨ (¬ p2598) ∨ (¬ p3641) ∨ (¬ p3698) ∨ (¬ p4610))
    : p2132 ∨ (¬ p3641) ∨ (¬ p4610) ∨ (¬ p3698) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4610 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48199 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step77415 (p2331 p2528 p2598 p2737 p2743 p2963 p3323 p3361 p3641 p4037 p4604 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73338 : p2963 ∨ p2331)
    (h73508 : p4037 ∨ p3323)
    (h71365 : (¬ p3641) ∨ (¬ p4037) ∨ (¬ p2528) ∨ (¬ p2963) ∨ (¬ p2598) ∨ (¬ p3361) ∨ (¬ p2743) ∨ (¬ p4604))
    : p2737 ∨ p2331 ∨ (¬ p3361) ∨ (¬ p2598) ∨ (¬ p2528) ∨ (¬ p3641) ∨ p3323 ∨ (¬ p4604) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h71365 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step77416 (p2528 p2737 p2743 p3367 p3641 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h45930 : (¬ p2528) ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3641))
    : (¬ p3367) ∨ p2737 ∨ (¬ p3641) ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45930 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step77417 (p2829 p3367 p3641 p3688 p4342 p4598 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h41645 : (¬ p3367) ∨ (¬ p3641) ∨ (¬ p3688) ∨ (¬ p4342) ∨ (¬ p4598))
    : (¬ p4342) ∨ p2829 ∨ (¬ p3641) ∨ (¬ p3367) ∨ (¬ p4598) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4342 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41645 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step77418 (p2440 p2542 p3083 p3367 p3641 p4256 : Prop)
    (h73542 : p4256 ∨ p3083)
    (h73270 : p2542 ∨ p2440)
    (h47518 : (¬ p2542) ∨ (¬ p3367) ∨ (¬ p3641) ∨ (¬ p4256))
    : (¬ p3641) ∨ (¬ p3367) ∨ p3083 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47518 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step77419 (p2363 p2528 p2598 p3641 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h64709 : (¬ p2528) ∨ (¬ p2598) ∨ (¬ p3641) ∨ (¬ p4347))
    : p2363 ∨ (¬ p3641) ∨ (¬ p2528) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h64709 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step77420 (p2651 p3166 p3172 p3641 p4437 p4753 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h50302 : (¬ p2651) ∨ (¬ p3172) ∨ (¬ p3641) ∨ (¬ p4437) ∨ (¬ p4753))
    : p3166 ∨ (¬ p3641) ∨ (¬ p4753) ∨ (¬ p2651) ∨ (¬ p4437) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h50302 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step77422 (p2177 p2299 p2437 p3641 p3742 p4343 p4404 p4712 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73234 : p2299 ∨ p2177)
    (h63530 : (¬ p2299) ∨ (¬ p3641) ∨ (¬ p3742) ∨ (¬ p4343) ∨ (¬ p4404) ∨ (¬ p4712))
    : (¬ p3641) ∨ p2437 ∨ (¬ p4404) ∨ (¬ p4712) ∨ p2177 ∨ (¬ p4343) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4404 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63530 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step77424 (p2727 p3189 p3641 p4360 p4437 p4753 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h55925 : (¬ p2727) ∨ (¬ p3641) ∨ (¬ p4360) ∨ (¬ p4437) ∨ (¬ p4753))
    : p3189 ∨ (¬ p3641) ∨ (¬ p2727) ∨ (¬ p4437) ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h55925 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step77437 (p2528 p2850 p3146 p3641 p3684 p3692 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73442 : p3684 ∨ p2850)
    (h55963 : (¬ p2528) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p3692))
    : (¬ p3641) ∨ p3146 ∨ (¬ p2528) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55963 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step77438 (p2220 p2459 p2608 p3146 p3367 p3641 p3692 p4120 p4420 p4524 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73522 : p4120 ∨ p2220)
    (h72962 : p4524)
    (h63052 : (¬ p2459) ∨ (¬ p2608) ∨ (¬ p3367) ∨ (¬ p3641) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4420) ∨ (¬ p4524))
    : p3146 ∨ (¬ p3641) ∨ (¬ p2459) ∨ (¬ p4420) ∨ (¬ p2608) ∨ p2220 ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u9 : p4524 := h72962;
    (Or.elim h63052 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u9)))))))))))))))))

theorem step77439 (p2210 p2598 p2753 p3073 p3449 p3641 p3860 p4149 p4261 p4877 p5122 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h73544 : p4261 ∨ p3073)
    (h61454 : (¬ p2210) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p3641) ∨ (¬ p3860) ∨ (¬ p4149) ∨ (¬ p4261) ∨ (¬ p4877) ∨ (¬ p5122))
    : (¬ p4149) ∨ (¬ p3641) ∨ (¬ p2753) ∨ (¬ p5122) ∨ (¬ p2210) ∨ (¬ p4877) ∨ p3449 ∨ (¬ p2598) ∨ p3073 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4149 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u10 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h61454 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step77442 (p2850 p3641 p3684 p4149 p5568 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h46998 : (¬ p3641) ∨ (¬ p3684) ∨ (¬ p4149) ∨ (¬ p5568))
    : (¬ p4149) ∨ (¬ p5568) ∨ (¬ p3641) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4149 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46998 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step77451 (p2528 p2608 p3379 p3641 p3954 p4030 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h63043 : (¬ p2528) ∨ (¬ p3379) ∨ (¬ p3641) ∨ (¬ p3954) ∨ (¬ p4030))
    : (¬ p3641) ∨ (¬ p2528) ∨ (¬ p3379) ∨ (¬ p4030) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63043 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step77454 (p2187 p2470 p2573 p2579 p3989 p4718 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73502 : p3989 ∨ p2187)
    (h66852 : (¬ p2579) ∨ (¬ p3989) ∨ (¬ p2470) ∨ (¬ p4718))
    : (¬ p2470) ∨ p2573 ∨ (¬ p4718) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h66852 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step77456 (p2470 p2528 p2553 p2573 p2579 p2588 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73282 : p2588 ∨ p2553)
    (h55501 : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2579) ∨ (¬ p2588))
    : (¬ p2470) ∨ p2573 ∨ p2553 ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h55501 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step77458 (p2363 p2470 p2573 p2579 p3422 p4157 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h59143 : (¬ p2363) ∨ (¬ p2470) ∨ (¬ p2579) ∨ (¬ p3422) ∨ (¬ p4157))
    : (¬ p2470) ∨ p2573 ∨ (¬ p3422) ∨ (¬ p4157) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h59143 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step77460 (p2440 p2470 p2542 p2573 p2579 p3083 p4256 p4715 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73270 : p2542 ∨ p2440)
    (h73542 : p4256 ∨ p3083)
    (h61726 : (¬ p2470) ∨ (¬ p2542) ∨ (¬ p2579) ∨ (¬ p4256) ∨ (¬ p4715))
    : (¬ p2470) ∨ p2573 ∨ p2440 ∨ p3083 ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61726 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step77461 (p2470 p2501 p2573 p2579 p3923 p4157 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h55365 : (¬ p2470) ∨ (¬ p2501) ∨ (¬ p2579) ∨ (¬ p3923) ∨ (¬ p4157))
    : p2573 ∨ (¬ p2470) ∨ (¬ p4157) ∨ (¬ p2501) ∨ (¬ p3923) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h55365 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step77463 (p2470 p2493 p2573 p2579 p3541 p3641 p3874 : Prop)
    (h73484 : p3874 ∨ p3641)
    (h73274 : p2579 ∨ p2573)
    (h54003 : (¬ p2470) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p3541) ∨ (¬ p3874))
    : p3641 ∨ (¬ p2470) ∨ (¬ p3541) ∨ p2573 ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54003 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step77467 (p2230 p2427 p2470 p2531 p2589 p4235 p4904 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h73536 : p4235 ∨ p2427)
    (h48137 : (¬ p2470) ∨ (¬ p2531) ∨ (¬ p2589) ∨ (¬ p4235) ∨ (¬ p4904))
    : (¬ p2531) ∨ (¬ p2470) ∨ p2230 ∨ (¬ p4904) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2531 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48137 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step77469 (p2230 p2470 p2531 p2563 p2589 p4110 p4509 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h73284 : p2589 ∨ p2230)
    (h49740 : (¬ p2470) ∨ (¬ p2531) ∨ (¬ p2589) ∨ (¬ p4110) ∨ (¬ p4509))
    : (¬ p2470) ∨ (¬ p2531) ∨ (¬ p4509) ∨ p2563 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2531 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49740 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step77470 (p2230 p2470 p2528 p2563 p2589 p4110 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h73516 : p4110 ∨ p2563)
    (h44014 : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2589) ∨ (¬ p4110))
    : (¬ p2470) ∨ (¬ p2528) ∨ p2230 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44014 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step77471 (p2230 p2363 p2470 p2528 p2589 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73284 : p2589 ∨ p2230)
    (h42652 : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2589) ∨ (¬ p4347))
    : (¬ p2470) ∨ p2363 ∨ p2230 ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42652 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step77472 (p2230 p2406 p2470 p2531 p2589 p3146 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h44883 : (¬ p2406) ∨ (¬ p2470) ∨ (¬ p2531) ∨ (¬ p2589) ∨ (¬ p3146))
    : (¬ p2406) ∨ (¬ p2470) ∨ (¬ p2531) ∨ (¬ p3146) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2531 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h44883 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step77473 (p2470 p2573 p2579 p3573 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h16580 : (¬ p2470) ∨ (¬ p2579) ∨ (¬ p3573))
    : (¬ p2470) ∨ p2573 ∨ (¬ p3573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h16580 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step77479 (p2470 p2553 p2573 p2579 p2588 p4157 p4405 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73274 : p2579 ∨ p2573)
    (h41858 : (¬ p2470) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p4157) ∨ (¬ p4405))
    : (¬ p2470) ∨ (¬ p4157) ∨ p2553 ∨ p2573 ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41858 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step77482 (p2470 p2528 p2573 p2579 p3422 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h45576 : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2579) ∨ (¬ p3422))
    : (¬ p2470) ∨ p2573 ∨ (¬ p3422) ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45576 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step77487 (p2406 p2470 p2509 p2573 p2579 p4715 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h61788 : (¬ p2406) ∨ (¬ p2470) ∨ (¬ p2509) ∨ (¬ p2579) ∨ (¬ p4715))
    : (¬ p2470) ∨ p2573 ∨ (¬ p2509) ∨ (¬ p2406) ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h61788 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step77489 (p2470 p2573 p2579 p2819 p4318 p4358 p4370 p5222 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73564 : p4358 ∨ p2819)
    (h60001 : (¬ p2470) ∨ (¬ p2579) ∨ (¬ p4318) ∨ (¬ p4358) ∨ (¬ p4370) ∨ (¬ p5222))
    : (¬ p4318) ∨ (¬ p2470) ∨ p2573 ∨ (¬ p5222) ∨ p2819 ∨ (¬ p4370) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4318 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h60001 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step77490 (p2187 p2470 p2573 p2579 p3989 p4157 p4718 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73502 : p3989 ∨ p2187)
    (h41992 : (¬ p2470) ∨ (¬ p2579) ∨ (¬ p3989) ∨ (¬ p4157) ∨ (¬ p4718))
    : p2573 ∨ (¬ p4157) ∨ (¬ p4718) ∨ (¬ p2470) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p4157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41992 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step77493 (p2470 p3389 p3540 p4186 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h6266 : (¬ p2470) ∨ (¬ p3540) ∨ (¬ p4186))
    : p3389 ∨ (¬ p2470) ∨ (¬ p4186) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3389) := (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4186 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h6266 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step77495 (p2470 p2528 p2573 p2579 p3016 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h56622 : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2579) ∨ (¬ p3016))
    : (¬ p2470) ∨ (¬ p3016) ∨ p2573 ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h56622 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step77497 (p2437 p2440 p2470 p3389 p3540 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h45868 : (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2470) ∨ (¬ p3540))
    : (¬ p2470) ∨ p3389 ∨ (¬ p2440) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45868 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step77499 (p2459 p2470 p2528 p3389 p3540 p4348 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h73562 : p4348 ∨ p2459)
    (h47920 : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3540) ∨ (¬ p4348))
    : (¬ p2470) ∨ p3389 ∨ p2459 ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47920 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step77502 (p2417 p2470 p3389 p3540 p4278 p4404 p4666 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h73546 : p4278 ∨ p2417)
    (h42032 : (¬ p2470) ∨ (¬ p3540) ∨ (¬ p4278) ∨ (¬ p4404) ∨ (¬ p4666))
    : p3389 ∨ (¬ p2470) ∨ p2417 ∨ (¬ p4404) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3389) := (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4404 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42032 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step77503 (p2177 p2299 p2470 p3389 p3540 p4370 p4712 p5307 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h73234 : p2299 ∨ p2177)
    (h53034 : (¬ p2299) ∨ (¬ p2470) ∨ (¬ p3540) ∨ (¬ p4370) ∨ (¬ p4712) ∨ (¬ p5307))
    : (¬ p5307) ∨ (¬ p2470) ∨ p3389 ∨ (¬ p4370) ∨ p2177 ∨ (¬ p4712) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h53034 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step77505 (p2470 p2573 p2579 p3016 p3641 p3874 p4750 : Prop)
    (h73484 : p3874 ∨ p3641)
    (h73274 : p2579 ∨ p2573)
    (h59128 : (¬ p2470) ∨ (¬ p2579) ∨ (¬ p3016) ∨ (¬ p3874) ∨ (¬ p4750))
    : p3641 ∨ (¬ p2470) ∨ (¬ p3016) ∨ (¬ p4750) ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h59128 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step77506 (p2470 p2930 p3389 p3527 p3540 p3548 p4404 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h73402 : p3540 ∨ p3389)
    (h41088 : (¬ p2470) ∨ (¬ p2930) ∨ (¬ p3540) ∨ (¬ p3548) ∨ (¬ p4404))
    : (¬ p4404) ∨ (¬ p2470) ∨ (¬ p2930) ∨ p3527 ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4404 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2930 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41088 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step77508 (p2264 p2470 p3389 p3540 p3553 p4327 p4404 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h73410 : p3553 ∨ p2264)
    (h48823 : (¬ p2470) ∨ (¬ p3540) ∨ (¬ p3553) ∨ (¬ p4327) ∨ (¬ p4404))
    : p3389 ∨ (¬ p2470) ∨ (¬ p4404) ∨ (¬ p4327) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3389) := (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4404 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4327 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48823 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step77517 (p2230 p2440 p2470 p2528 p2542 p2589 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73284 : p2589 ∨ p2230)
    (h55889 : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2542) ∨ (¬ p2589))
    : (¬ p2470) ∨ (¬ p2528) ∨ p2440 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55889 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step77523 (p2470 p2881 p3389 p3540 p3570 p4370 p4647 p5307 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h73418 : p3570 ∨ p2881)
    (h41244 : (¬ p2470) ∨ (¬ p3540) ∨ (¬ p3570) ∨ (¬ p4370) ∨ (¬ p4647) ∨ (¬ p5307))
    : (¬ p5307) ∨ (¬ p2470) ∨ (¬ p4647) ∨ p3389 ∨ (¬ p4370) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41244 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step77527 (p2274 p2470 p2573 p2579 p3096 p3097 p4157 p4405 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73352 : p3097 ∨ p2274)
    (h57098 : (¬ p2470) ∨ (¬ p2579) ∨ (¬ p3096) ∨ (¬ p3097) ∨ (¬ p4157) ∨ (¬ p4405))
    : (¬ p2470) ∨ p2573 ∨ (¬ p4157) ∨ (¬ p4405) ∨ (¬ p3096) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h57098 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step77528 (p2440 p2470 p2573 p2579 p3016 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h59961 : (¬ p2440) ∨ (¬ p2470) ∨ (¬ p2579) ∨ (¬ p3016))
    : (¬ p2470) ∨ (¬ p3016) ∨ (¬ p2440) ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h59961 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step77535 (p2383 p2470 p2665 p2668 p3016 p3324 p3574 p4194 p4973 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73386 : p3324 ∨ p2668)
    (h66996 : (¬ p2383) ∨ (¬ p2470) ∨ (¬ p3324) ∨ (¬ p2665) ∨ (¬ p4973) ∨ (¬ p4194) ∨ (¬ p3574))
    : (¬ p2383) ∨ (¬ p2470) ∨ (¬ p4194) ∨ p3016 ∨ (¬ p2665) ∨ p2668 ∨ (¬ p4973) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h66996 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u7)))))))))))))))

theorem step77536 (p2470 p2663 p2946 p2952 p3083 p4256 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73542 : p4256 ∨ p3083)
    (h69609 : (¬ p2470) ∨ (¬ p2952) ∨ (¬ p4256) ∨ (¬ p2663))
    : (¬ p2470) ∨ p2946 ∨ (¬ p2663) ∨ p3083 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69609 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step77538 (p2230 p2470 p2589 p3073 p3146 p3692 p4370 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73284 : p2589 ∨ p2230)
    (h48136 : (¬ p2470) ∨ (¬ p2589) ∨ (¬ p3073) ∨ (¬ p3692) ∨ (¬ p4370))
    : (¬ p3073) ∨ p3146 ∨ (¬ p2470) ∨ (¬ p4370) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48136 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step77540 (p2230 p2440 p2470 p2509 p2542 p2589 p4811 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h73270 : p2542 ∨ p2440)
    (h58911 : (¬ p2470) ∨ (¬ p2509) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p4811))
    : (¬ p2470) ∨ (¬ p2509) ∨ (¬ p4811) ∨ p2230 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h58911 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step77541 (p2177 p2230 p2299 p2440 p2470 p2542 p2589 p4404 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h73270 : p2542 ∨ p2440)
    (h73284 : p2589 ∨ p2230)
    (h46123 : (¬ p2299) ∨ (¬ p2470) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p4404))
    : (¬ p2470) ∨ (¬ p4404) ∨ p2177 ∨ p2440 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4404 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46123 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step77542 (p2230 p2470 p2589 p4607 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h10277 : (¬ p2470) ∨ (¬ p2589) ∨ (¬ p4607))
    : (¬ p2470) ∨ (¬ p4607) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4607 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10277 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step77545 (p2230 p2470 p2531 p2589 p2850 p3146 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h52148 : (¬ p2470) ∨ (¬ p2531) ∨ (¬ p2589) ∨ (¬ p2850) ∨ (¬ p3146))
    : (¬ p2850) ∨ (¬ p2470) ∨ (¬ p3146) ∨ p2230 ∨ (¬ p2531) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2531 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h52148 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step77547 (p2187 p2192 p2210 p2459 p2470 p2528 p3555 p3989 p4173 p4348 p4503 p5190 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73502 : p3989 ∨ p2187)
    (h73528 : p4173 ∨ p2192)
    (h73562 : p4348 ∨ p2459)
    (h54184 : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3555) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p5190))
    : (¬ p2470) ∨ p2210 ∨ (¬ p5190) ∨ p2187 ∨ (¬ p2528) ∨ p2192 ∨ p2459 ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h54184 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step77551 (p2295 p2470 p2553 p2588 p3019 p3083 p4256 : Prop)
    (h73542 : p4256 ∨ p3083)
    (h73282 : p2588 ∨ p2553)
    (h47403 : (¬ p2295) ∨ (¬ p2470) ∨ (¬ p2588) ∨ (¬ p3019) ∨ (¬ p4256))
    : (¬ p2470) ∨ (¬ p2295) ∨ p3083 ∨ (¬ p3019) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47403 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step77553 (p3422 p4390 p5223 : Prop)
    (h73966 : p5223 ∨ (¬ p3422))
    (h8877 : p4390 ∨ (¬ p5223))
    : p4390 ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4390) := (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5223 := (Or.elim h73966 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h8877 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step77555 (p3422 p5223 p5224 : Prop)
    (h73966 : p5223 ∨ (¬ p3422))
    (h8880 : (¬ p5223) ∨ p5224)
    : (¬ p3422) ∨ p5224 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3422 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5224) := (fun h => hn (Or.inr h));
    let u2 : p5223 := (Or.elim h73966 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h8880 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step77556 (p3422 p5223 p5225 : Prop)
    (h73966 : p5223 ∨ (¬ p3422))
    (h8881 : (¬ p5223) ∨ p5225)
    : (¬ p3422) ∨ p5225 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3422 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5225) := (fun h => hn (Or.inr h));
    let u2 : p5223 := (Or.elim h73966 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h8881 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step77557 (p2573 p2579 p3363 p3422 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h20116 : (¬ p2579) ∨ (¬ p3363) ∨ (¬ p3422))
    : p2573 ∨ (¬ p3422) ∨ (¬ p3363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h20116 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u1)))))))

theorem step77562 (p2651 p2657 p2850 p3016 p3422 p3574 p3684 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73422 : p3574 ∨ p3016)
    (h73442 : p3684 ∨ p2850)
    (h53620 : (¬ p2657) ∨ (¬ p3422) ∨ (¬ p3574) ∨ (¬ p3684))
    : p2651 ∨ p3016 ∨ (¬ p3422) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53620 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step77564 (p2396 p2573 p2579 p3201 p3422 p3876 p3921 p4107 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73274 : p2579 ∨ p2573)
    (h73514 : p4107 ∨ p2396)
    (h51417 : (¬ p2579) ∨ (¬ p3422) ∨ (¬ p3876) ∨ (¬ p3921) ∨ (¬ p4107))
    : p3201 ∨ p2573 ∨ p2396 ∨ (¬ p3422) ∨ (¬ p3921) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h51417 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step77567 (p2210 p2573 p2579 p2881 p2891 p3422 p3641 p3874 p4438 p5193 : Prop)
    (h73484 : p3874 ∨ p3641)
    (h73274 : p2579 ∨ p2573)
    (h50451 : (¬ p2210) ∨ (¬ p2579) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3422) ∨ (¬ p3874) ∨ (¬ p4438) ∨ (¬ p5193))
    : p3641 ∨ p2573 ∨ (¬ p5193) ∨ (¬ p2210) ∨ (¬ p3422) ∨ (¬ p4438) ∨ (¬ p2891) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h50451 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step77568 (p2573 p2579 p2881 p3201 p3399 p3422 p3527 p3570 p3876 p4647 p5193 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73274 : p2579 ∨ p2573)
    (h73418 : p3570 ∨ p2881)
    (h53748 : (¬ p2579) ∨ (¬ p3399) ∨ (¬ p3422) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p3876) ∨ (¬ p4647) ∨ (¬ p5193))
    : (¬ p3527) ∨ p3201 ∨ (¬ p4647) ∨ p2573 ∨ p2881 ∨ (¬ p3422) ∨ (¬ p5193) ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h53748 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step77569 (p2241 p2247 p2598 p3189 p3256 p3422 p3564 p4118 p4330 p4360 p4733 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h73566 : p4360 ∨ p3189)
    (h73226 : p2247 ∨ p2241)
    (h50632 : (¬ p2247) ∨ (¬ p2598) ∨ (¬ p3422) ∨ (¬ p3564) ∨ (¬ p4118) ∨ (¬ p4330) ∨ (¬ p4360) ∨ (¬ p4733))
    : (¬ p3564) ∨ p3256 ∨ (¬ p4330) ∨ p3189 ∨ p2241 ∨ (¬ p2598) ∨ (¬ p3422) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50632 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step77574 (p2177 p2299 p2573 p2579 p3201 p3422 p3876 p3921 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73274 : p2579 ∨ p2573)
    (h73234 : p2299 ∨ p2177)
    (h43886 : (¬ p2299) ∨ (¬ p2579) ∨ (¬ p3422) ∨ (¬ p3876) ∨ (¬ p3921))
    : p3201 ∨ p2573 ∨ p2177 ∨ (¬ p3921) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43886 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step77577 (p2230 p2440 p2573 p2579 p3422 p4753 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h48138 : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2579) ∨ (¬ p3422) ∨ (¬ p4753))
    : (¬ p2230) ∨ p2573 ∨ (¬ p4753) ∨ (¬ p2440) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h48138 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step77580 (p2573 p2579 p2598 p3422 p4108 p4733 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h50054 : (¬ p2579) ∨ (¬ p2598) ∨ (¬ p3422) ∨ (¬ p4108) ∨ (¬ p4733))
    : (¬ p3422) ∨ p2573 ∨ (¬ p2598) ∨ (¬ p4733) ∨ (¬ p4108) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3422 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h50054 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step77581 (p2573 p2579 p3367 p3422 p3905 p4734 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h72735 : p4734)
    (h50224 : (¬ p2579) ∨ (¬ p3367) ∨ (¬ p3422) ∨ (¬ p3905) ∨ (¬ p4734))
    : (¬ p3367) ∨ (¬ p3905) ∨ p2573 ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4734 := h72735;
    (Or.elim h50224 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step77585 (p2573 p2579 p3276 p3355 p3422 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h45419 : (¬ p2579) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3422))
    : (¬ p3355) ∨ (¬ p3276) ∨ p2573 ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3355 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45419 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step77587 (p2573 p2579 p2850 p3355 p3422 p3684 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73442 : p3684 ∨ p2850)
    (h53899 : (¬ p2579) ∨ (¬ p3355) ∨ (¬ p3422) ∨ (¬ p3684))
    : (¬ p3355) ∨ p2573 ∨ (¬ p3422) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3355 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53899 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step77589 (p2573 p2579 p3276 p3422 p3905 p4425 p5160 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73578 : p4425 ∨ p3276)
    (h54871 : (¬ p2579) ∨ (¬ p3422) ∨ (¬ p3905) ∨ (¬ p4425) ∨ (¬ p5160))
    : (¬ p5160) ∨ p2573 ∨ p3276 ∨ (¬ p3905) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5160 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h54871 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step77591 (p2573 p2579 p2696 p3422 p3905 p4749 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h41841 : (¬ p2579) ∨ (¬ p2696) ∨ (¬ p3422) ∨ (¬ p3905) ∨ (¬ p4749))
    : p2573 ∨ (¬ p3422) ∨ (¬ p3905) ∨ (¬ p2696) ∨ (¬ p4749) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41841 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step77593 (p2573 p2579 p2761 p3266 p3347 p3370 p3422 p3516 p4257 p4377 p4444 p4697 p4988 p5160 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73274 : p2579 ∨ p2573)
    (h63575 : (¬ p2579) ∨ (¬ p2761) ∨ (¬ p3347) ∨ (¬ p3370) ∨ (¬ p3422) ∨ (¬ p3516) ∨ (¬ p4257) ∨ (¬ p4377) ∨ (¬ p4444) ∨ (¬ p4697) ∨ (¬ p4988) ∨ (¬ p5160))
    : p3266 ∨ (¬ p5160) ∨ (¬ p4697) ∨ (¬ p3422) ∨ (¬ p3516) ∨ (¬ p4257) ∨ (¬ p3347) ∨ (¬ p4377) ∨ (¬ p4988) ∨ (¬ p2761) ∨ p2573 ∨ (¬ p3370) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u13 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h63575 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u8))) (fun r10 => (False.elim (r10 u1)))))))))))))))))))))))))

theorem step77594 (p2132 p2573 p2579 p3422 p3475 p3905 p5052 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h49895 : (¬ p2132) ∨ (¬ p2579) ∨ (¬ p3422) ∨ (¬ p3475) ∨ (¬ p3905) ∨ (¬ p5052))
    : (¬ p3905) ∨ p2573 ∨ (¬ p5052) ∨ (¬ p3475) ∨ (¬ p2132) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3905 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5052 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h49895 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step77597 (p2210 p2241 p2247 p2573 p2579 p2744 p2891 p3201 p3366 p3422 p3876 p3905 p4647 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73274 : p2579 ∨ p2573)
    (h73226 : p2247 ∨ p2241)
    (h63894 : (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2579) ∨ (¬ p2744) ∨ (¬ p2891) ∨ (¬ p3366) ∨ (¬ p3422) ∨ (¬ p3876) ∨ (¬ p3905) ∨ (¬ p4647))
    : p3201 ∨ (¬ p3422) ∨ (¬ p2210) ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p2891) ∨ (¬ p3905) ∨ (¬ p4647) ∨ p2573 ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u12 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h63894 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step77599 (p2573 p2579 p2946 p3146 p3156 p3422 p3905 p4697 p4786 p5160 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h52153 : (¬ p2579) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3422) ∨ (¬ p3905) ∨ (¬ p4697) ∨ (¬ p4786) ∨ (¬ p5160))
    : (¬ p5160) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p2946) ∨ p2573 ∨ (¬ p4697) ∨ (¬ p3422) ∨ (¬ p4786) ∨ (¬ p3905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5160 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h52153 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step77600 (p2352 p3201 p3422 p3876 p3921 p4405 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h48342 : (¬ p2352) ∨ (¬ p3422) ∨ (¬ p3876) ∨ (¬ p3921) ∨ (¬ p4405))
    : p3201 ∨ (¬ p3422) ∨ (¬ p4405) ∨ (¬ p3921) ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48342 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step77606 (p2459 p2598 p3399 p3422 p3527 p3548 p3564 p4330 p4348 p4366 p4733 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h73562 : p4348 ∨ p2459)
    (h73570 : p4366 ∨ p3399)
    (h50641 : (¬ p2598) ∨ (¬ p3422) ∨ (¬ p3548) ∨ (¬ p3564) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4366) ∨ (¬ p4733))
    : (¬ p3564) ∨ (¬ p3422) ∨ (¬ p2598) ∨ p3527 ∨ p2459 ∨ (¬ p4330) ∨ (¬ p4733) ∨ p3399 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h50641 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step77609 (p2493 p2499 p2528 p2534 p3422 p3641 p3874 : Prop)
    (h73484 : p3874 ∨ p3641)
    (h73268 : p2534 ∨ p2528)
    (h73260 : p2499 ∨ p2493)
    (h56392 : (¬ p2499) ∨ (¬ p2534) ∨ (¬ p3422) ∨ (¬ p3874))
    : p3641 ∨ p2528 ∨ (¬ p3422) ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56392 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step77610 (p2528 p2534 p2573 p2579 p3422 p3641 p3874 : Prop)
    (h73484 : p3874 ∨ p3641)
    (h73268 : p2534 ∨ p2528)
    (h73274 : p2579 ∨ p2573)
    (h56551 : (¬ p2534) ∨ (¬ p2579) ∨ (¬ p3422) ∨ (¬ p3874))
    : p3641 ∨ p2528 ∨ (¬ p3422) ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56551 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step77613 (p2245 p2352 p2459 p2598 p3166 p3172 p3256 p3422 p4118 p4133 p4733 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h73520 : p4118 ∨ p3256)
    (h64320 : (¬ p2245) ∨ (¬ p2352) ∨ (¬ p2459) ∨ (¬ p2598) ∨ (¬ p3172) ∨ (¬ p3422) ∨ (¬ p4118) ∨ (¬ p4133) ∨ (¬ p4733))
    : (¬ p2245) ∨ p3166 ∨ (¬ p2598) ∨ (¬ p4133) ∨ (¬ p2352) ∨ (¬ p2459) ∨ p3256 ∨ (¬ p4733) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h64320 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step77614 (p2245 p2352 p2598 p3146 p3166 p3172 p3256 p3422 p4118 p4134 p4733 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h73520 : p4118 ∨ p3256)
    (h53193 : (¬ p2245) ∨ (¬ p2352) ∨ (¬ p2598) ∨ (¬ p3146) ∨ (¬ p3172) ∨ (¬ p3422) ∨ (¬ p4118) ∨ (¬ p4134) ∨ (¬ p4733))
    : p3166 ∨ (¬ p2352) ∨ (¬ p2245) ∨ (¬ p3422) ∨ (¬ p2598) ∨ (¬ p4134) ∨ (¬ p4733) ∨ p3256 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h53193 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step77617 (p2145 p2220 p2352 p2459 p2598 p3256 p3422 p4118 p4120 p4133 p4311 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h73522 : p4120 ∨ p2220)
    (h65123 : (¬ p2145) ∨ (¬ p2352) ∨ (¬ p2459) ∨ (¬ p2598) ∨ (¬ p3422) ∨ (¬ p4118) ∨ (¬ p4120) ∨ (¬ p4133) ∨ (¬ p4311))
    : (¬ p2145) ∨ (¬ p3422) ∨ (¬ p4133) ∨ (¬ p2459) ∨ p3256 ∨ p2220 ∨ (¬ p2598) ∨ (¬ p4311) ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2145 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h65123 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step77619 (p2177 p2352 p2598 p3201 p3422 p3876 p4502 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73604 : p4502 ∨ (¬ p2177))
    (h66815 : (¬ p3422) ∨ (¬ p4502) ∨ (¬ p2352) ∨ (¬ p3876) ∨ (¬ p2598))
    : p3201 ∨ (¬ p3422) ∨ (¬ p2598) ∨ (¬ p2177) ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4502 := (Or.elim h73604 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h66815 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step77620 (p2331 p2651 p2963 p3422 p4389 p4753 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h41889 : (¬ p2651) ∨ (¬ p2963) ∨ (¬ p3422) ∨ (¬ p4389) ∨ (¬ p4753))
    : p2331 ∨ (¬ p3422) ∨ (¬ p2651) ∨ (¬ p4389) ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41889 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step77623 (p2437 p2598 p3016 p3422 p3574 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h42888 : (¬ p2437) ∨ (¬ p2598) ∨ (¬ p3422) ∨ (¬ p3574))
    : (¬ p2437) ∨ p3016 ∨ (¬ p2598) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42888 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step77624 (p2437 p2911 p3016 p3422 p3475 p3574 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h43522 : (¬ p2437) ∨ (¬ p2911) ∨ (¬ p3422) ∨ (¬ p3475) ∨ (¬ p3574))
    : (¬ p2437) ∨ (¬ p2911) ∨ (¬ p3422) ∨ p3016 ∨ (¬ p3475) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43522 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step77625 (p2177 p2299 p3016 p3201 p3422 p3574 p3876 p3921 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73422 : p3574 ∨ p3016)
    (h73234 : p2299 ∨ p2177)
    (h60427 : (¬ p2299) ∨ (¬ p3422) ∨ (¬ p3574) ∨ (¬ p3876) ∨ (¬ p3921))
    : p3201 ∨ p3016 ∨ (¬ p3921) ∨ p2177 ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60427 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step77626 (p2737 p2743 p3016 p3367 p3422 p3574 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73422 : p3574 ∨ p3016)
    (h53466 : (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3422) ∨ (¬ p3574))
    : (¬ p3422) ∨ p2737 ∨ p3016 ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3422 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h53466 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step77628 (p2598 p2696 p3016 p3365 p3422 p3574 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h73422 : p3574 ∨ p3016)
    (h53743 : (¬ p2598) ∨ (¬ p3365) ∨ (¬ p3422) ∨ (¬ p3574))
    : (¬ p3422) ∨ p2696 ∨ p3016 ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3422 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h53743 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step77629 (p2651 p2657 p3016 p3422 p3475 p3574 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73422 : p3574 ∨ p3016)
    (h71367 : (¬ p3422) ∨ (¬ p3574) ∨ (¬ p2657) ∨ (¬ p3475))
    : p2651 ∨ p3016 ∨ (¬ p3422) ∨ (¬ p3475) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71367 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step77630 (p2663 p3016 p3201 p3389 p3422 p3574 p3876 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73422 : p3574 ∨ p3016)
    (h54468 : (¬ p2663) ∨ (¬ p3389) ∨ (¬ p3422) ∨ (¬ p3574) ∨ (¬ p3876))
    : (¬ p3389) ∨ p3201 ∨ (¬ p2663) ∨ (¬ p3422) ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54468 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step77638 (p2363 p2493 p2499 p3422 p3641 p3874 p4347 p4432 : Prop)
    (h73484 : p3874 ∨ p3641)
    (h73560 : p4347 ∨ p2363)
    (h73260 : p2499 ∨ p2493)
    (h58952 : (¬ p2499) ∨ (¬ p3422) ∨ (¬ p3874) ∨ (¬ p4347) ∨ (¬ p4432))
    : p3641 ∨ p2363 ∨ p2493 ∨ (¬ p4432) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h58952 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step77644 (p2284 p2578 p2850 p3422 p3684 p3952 p4356 p4702 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73442 : p3684 ∨ p2850)
    (h63583 : (¬ p2578) ∨ (¬ p3422) ∨ (¬ p3684) ∨ (¬ p3952) ∨ (¬ p4356) ∨ (¬ p4702))
    : p2284 ∨ (¬ p2578) ∨ (¬ p4702) ∨ (¬ p3422) ∨ (¬ p4356) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2284) := (fun h => hn (Or.inl h));
    let u1 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h63583 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step77648 (p2573 p2579 p2662 p2727 p2745 p3422 p3475 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73274 : p2579 ∨ p2573)
    (h41897 : (¬ p2579) ∨ (¬ p2662) ∨ (¬ p2745) ∨ (¬ p3422) ∨ (¬ p3475) ∨ (¬ p4111))
    : p2727 ∨ (¬ p3475) ∨ (¬ p3422) ∨ p2573 ∨ (¬ p2745) ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p3475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41897 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step77649 (p2210 p2573 p2579 p2881 p3201 p3422 p3527 p3570 p3876 p4431 p4647 p5193 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73274 : p2579 ∨ p2573)
    (h73418 : p3570 ∨ p2881)
    (h48887 : (¬ p2210) ∨ (¬ p2579) ∨ (¬ p3422) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p3876) ∨ (¬ p4431) ∨ (¬ p4647) ∨ (¬ p5193))
    : (¬ p3527) ∨ p3201 ∨ (¬ p3422) ∨ (¬ p4431) ∨ p2573 ∨ p2881 ∨ (¬ p4647) ∨ (¬ p5193) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h48887 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step77651 (p2352 p2459 p2598 p3073 p3422 p3449 p3860 p4133 p4261 p4733 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h73482 : p3860 ∨ p3449)
    (h64783 : (¬ p2352) ∨ (¬ p2459) ∨ (¬ p2598) ∨ (¬ p3422) ∨ (¬ p3860) ∨ (¬ p4133) ∨ (¬ p4261) ∨ (¬ p4733))
    : (¬ p2598) ∨ (¬ p2352) ∨ p3073 ∨ (¬ p2459) ∨ (¬ p3422) ∨ (¬ p4733) ∨ p3449 ∨ (¬ p4133) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h64783 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step77653 (p2352 p2598 p3073 p3146 p3422 p3449 p3860 p4134 p4261 p4733 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h73482 : p3860 ∨ p3449)
    (h62486 : (¬ p2352) ∨ (¬ p2598) ∨ (¬ p3146) ∨ (¬ p3422) ∨ (¬ p3860) ∨ (¬ p4134) ∨ (¬ p4261) ∨ (¬ p4733))
    : (¬ p2598) ∨ p3073 ∨ (¬ p4134) ∨ p3449 ∨ (¬ p4733) ∨ (¬ p3146) ∨ (¬ p3422) ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62486 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step77655 (p3422 p3564 p3641 p3874 p4432 p4603 : Prop)
    (h73484 : p3874 ∨ p3641)
    (h53882 : (¬ p3422) ∨ (¬ p3564) ∨ (¬ p3874) ∨ (¬ p4432) ∨ (¬ p4603))
    : p3641 ∨ (¬ p3564) ∨ (¬ p4603) ∨ (¬ p4432) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4603 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h53882 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step77656 (p2497 p3319 p3422 p3564 p4026 p5214 : Prop)
    (h73504 : p4026 ∨ p3319)
    (h48345 : (¬ p2497) ∨ (¬ p3422) ∨ (¬ p3564) ∨ (¬ p4026) ∨ (¬ p5214))
    : (¬ p3564) ∨ p3319 ∨ (¬ p2497) ∨ (¬ p5214) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3319) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5214 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h48345 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step77658 (p2156 p2850 p3422 p3646 p3684 p4203 p4533 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73436 : p3646 ∨ p2156)
    (h50151 : (¬ p3422) ∨ (¬ p3646) ∨ (¬ p3684) ∨ (¬ p4203) ∨ (¬ p4533))
    : p2850 ∨ p2156 ∨ (¬ p4203) ∨ (¬ p3422) ∨ (¬ p4533) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h50151 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step77661 (p2241 p2352 p2598 p2750 p2753 p3093 p3309 p3422 p3549 p3591 p4405 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73406 : p3549 ∨ p3309)
    (h62915 : (¬ p2241) ∨ (¬ p2352) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3422) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4405))
    : p3093 ∨ (¬ p2241) ∨ (¬ p3422) ∨ (¬ p2750) ∨ p3309 ∨ (¬ p4405) ∨ (¬ p2598) ∨ (¬ p2352) ∨ (¬ p2753) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62915 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step77665 (p2307 p2313 p2553 p2850 p3422 p3684 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73442 : p3684 ∨ p2850)
    (h44037 : (¬ p2313) ∨ (¬ p2553) ∨ (¬ p3422) ∨ (¬ p3684))
    : (¬ p2553) ∨ p2307 ∨ (¬ p3422) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44037 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step77667 (p2352 p2363 p2850 p3422 p3684 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h61997 : (¬ p2352) ∨ (¬ p2363) ∨ (¬ p3422) ∨ (¬ p3684))
    : (¬ p3422) ∨ p2850 ∨ (¬ p2363) ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3422 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h61997 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step77668 (p2187 p2352 p2850 p3422 p3684 p3989 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73502 : p3989 ∨ p2187)
    (h51318 : (¬ p2352) ∨ (¬ p3422) ∨ (¬ p3684) ∨ (¬ p3989))
    : p2850 ∨ (¬ p3422) ∨ (¬ p2352) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h51318 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step77670 (p2295 p2352 p2668 p3324 p3422 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h43210 : (¬ p2295) ∨ (¬ p2352) ∨ (¬ p3324) ∨ (¬ p3422))
    : (¬ p2295) ∨ (¬ p3422) ∨ (¬ p2352) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43210 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step77671 (p2352 p2383 p2387 p2577 p3422 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h71370 : (¬ p2387) ∨ (¬ p2352) ∨ (¬ p3422) ∨ (¬ p2577))
    : (¬ p2577) ∨ (¬ p3422) ∨ p2383 ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2577 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h71370 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step77674 (p2352 p2383 p2387 p2850 p3422 p3684 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73246 : p2387 ∨ p2383)
    (h55646 : (¬ p2352) ∨ (¬ p2387) ∨ (¬ p3422) ∨ (¬ p3684))
    : p2850 ∨ (¬ p3422) ∨ p2383 ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h55646 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step77677 (p2363 p2528 p2534 p3422 p3641 p3874 : Prop)
    (h73484 : p3874 ∨ p3641)
    (h73268 : p2534 ∨ p2528)
    (h47901 : (¬ p2363) ∨ (¬ p2534) ∨ (¬ p3422) ∨ (¬ p3874))
    : p3641 ∨ p2528 ∨ (¬ p2363) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47901 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step77679 (p2210 p2352 p2598 p2881 p2891 p3422 p3486 p3555 p3570 p4133 p4733 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73398 : p3486 ∨ p2891)
    (h73418 : p3570 ∨ p2881)
    (h51554 : (¬ p2352) ∨ (¬ p2598) ∨ (¬ p3422) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4133) ∨ (¬ p4733))
    : p2210 ∨ (¬ p2598) ∨ (¬ p2352) ∨ (¬ p4133) ∨ (¬ p3422) ∨ p2891 ∨ p2881 ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h51554 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step77681 (p2352 p2598 p2881 p2901 p2946 p2952 p3422 p3570 p4133 p4320 p4789 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73330 : p2952 ∨ p2946)
    (h73418 : p3570 ∨ p2881)
    (h65125 : (¬ p2352) ∨ (¬ p2598) ∨ (¬ p2952) ∨ (¬ p3422) ∨ (¬ p3570) ∨ (¬ p4133) ∨ (¬ p4320) ∨ (¬ p4789))
    : p2901 ∨ (¬ p2352) ∨ (¬ p4789) ∨ p2946 ∨ p2881 ∨ (¬ p3422) ∨ (¬ p4133) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h65125 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step77682 (p2210 p2598 p2753 p3246 p3399 p3422 p3564 p3690 p4366 p4621 p4877 p4909 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73446 : p3690 ∨ p3246)
    (h51489 : (¬ p2210) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p3422) ∨ (¬ p3564) ∨ (¬ p3690) ∨ (¬ p4366) ∨ (¬ p4621) ∨ (¬ p4877) ∨ (¬ p4909))
    : p3399 ∨ (¬ p2753) ∨ (¬ p4909) ∨ (¬ p3564) ∨ (¬ p2598) ∨ p3246 ∨ (¬ p4877) ∨ (¬ p3422) ∨ (¬ p4621) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4909 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h51489 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step77683 (p2598 p3266 p3286 p3292 p3422 p3564 p4330 p4789 p5284 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h42610 : (¬ p2598) ∨ (¬ p3266) ∨ (¬ p3292) ∨ (¬ p3422) ∨ (¬ p3564) ∨ (¬ p4330) ∨ (¬ p4789) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p3266) ∨ (¬ p2598) ∨ (¬ p4330) ∨ (¬ p4789) ∨ (¬ p3422) ∨ (¬ p3564) ∨ p3286 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h42610 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step77684 (p2493 p2499 p2608 p3093 p3422 p3591 p5214 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73260 : p2499 ∨ p2493)
    (h65953 : (¬ p2499) ∨ (¬ p3422) ∨ (¬ p5214) ∨ (¬ p3591) ∨ (¬ p2608))
    : p3093 ∨ (¬ p2608) ∨ (¬ p3422) ∨ p2493 ∨ (¬ p5214) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5214 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h65953 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step77691 (p2295 p2553 p3422 p3568 p4194 p4753 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h49419 : (¬ p2553) ∨ (¬ p3422) ∨ (¬ p3568) ∨ (¬ p4194) ∨ (¬ p4753))
    : p2295 ∨ (¬ p2553) ∨ (¬ p3422) ∨ (¬ p4753) ∨ (¬ p4194) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2295) := (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49419 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step77693 (p2427 p2850 p3422 p3684 p4203 p4235 p4555 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73536 : p4235 ∨ p2427)
    (h41106 : (¬ p3422) ∨ (¬ p3684) ∨ (¬ p4203) ∨ (¬ p4235) ∨ (¬ p4555))
    : p2850 ∨ p2427 ∨ (¬ p4555) ∨ (¬ p3422) ∨ (¬ p4203) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41106 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step77694 (p2132 p2138 p2598 p3422 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h67195 : (¬ p3422) ∨ (¬ p2598) ∨ (¬ p2138))
    : p2132 ∨ (¬ p3422) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h67195 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step77695 (p2737 p2743 p3367 p3422 p3564 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h63728 : (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3422) ∨ (¬ p3564))
    : (¬ p3564) ∨ p2737 ∨ (¬ p3422) ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h63728 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step77696 (p2578 p2641 p2667 p2727 p3422 p4154 p4753 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h42465 : (¬ p2578) ∨ (¬ p2667) ∨ (¬ p2727) ∨ (¬ p3422) ∨ (¬ p4154) ∨ (¬ p4753))
    : p2641 ∨ (¬ p3422) ∨ (¬ p2727) ∨ (¬ p2667) ∨ (¬ p2578) ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42465 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step77703 (p2252 p2264 p2459 p2598 p2750 p2753 p2807 p3414 p3422 p3553 p3564 p4330 p4348 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h73562 : p4348 ∨ p2459)
    (h73392 : p3414 ∨ p2807)
    (h64584 : (¬ p2252) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3414) ∨ (¬ p3422) ∨ (¬ p3553) ∨ (¬ p3564) ∨ (¬ p4330) ∨ (¬ p4348))
    : p2264 ∨ (¬ p2753) ∨ p2459 ∨ (¬ p2598) ∨ (¬ p3422) ∨ (¬ p2750) ∨ p2807 ∨ (¬ p2252) ∨ (¬ p3564) ∨ (¬ p4330) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2264) := (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h64584 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u11)))))))))))))))))))))

theorem step77705 (p2553 p2608 p3379 p3422 p3954 p4030 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h44770 : (¬ p2553) ∨ (¬ p3379) ∨ (¬ p3422) ∨ (¬ p3954) ∨ (¬ p4030))
    : p2608 ∨ (¬ p2553) ∨ (¬ p4030) ∨ (¬ p3379) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h44770 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step77706 (p2839 p3367 p3422 p3583 p3698 p4717 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h41062 : (¬ p3367) ∨ (¬ p3422) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p4717))
    : (¬ p3367) ∨ p2839 ∨ (¬ p3422) ∨ (¬ p3698) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41062 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step77708 (p2493 p2499 p2850 p3379 p3422 p3452 p3684 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73394 : p3452 ∨ p3379)
    (h73260 : p2499 ∨ p2493)
    (h57059 : (¬ p2499) ∨ (¬ p3422) ∨ (¬ p3452) ∨ (¬ p3684))
    : p2850 ∨ p3379 ∨ p2493 ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h57059 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step77711 (p2192 p2850 p3422 p3684 p4173 p4203 p4629 : Prop)
    (h73528 : p4173 ∨ p2192)
    (h73442 : p3684 ∨ p2850)
    (h42511 : (¬ p3422) ∨ (¬ p3684) ∨ (¬ p4173) ∨ (¬ p4203) ∨ (¬ p4629))
    : p2192 ∨ p2850 ∨ (¬ p4203) ∨ (¬ p3422) ∨ (¬ p4629) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2192) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42511 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step77712 (p2373 p2440 p2510 p2531 p3016 p3156 p3422 p3497 p4699 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h73712 : p4699 ∨ (¬ p2440))
    (h66902 : (¬ p3422) ∨ (¬ p2510) ∨ (¬ p2531) ∨ p3016 ∨ (¬ p2373) ∨ (¬ p4699) ∨ (¬ p3497))
    : (¬ p2510) ∨ p3156 ∨ (¬ p2531) ∨ (¬ p2440) ∨ p3016 ∨ (¬ p2373) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2510 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2531 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4699 := (Or.elim h73712 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h66902 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u4 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (False.elim (r5 u7)))))))))))))))

theorem step77718 (p2274 p3201 p3422 p3876 p3921 p3958 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h51859 : (¬ p2274) ∨ (¬ p3422) ∨ (¬ p3876) ∨ (¬ p3921) ∨ (¬ p3958))
    : p3201 ∨ (¬ p2274) ∨ (¬ p3958) ∨ (¬ p3422) ∨ (¬ p3921) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h51859 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step77722 (p2470 p2553 p3422 p3641 p3874 : Prop)
    (h73484 : p3874 ∨ p3641)
    (h47895 : (¬ p2470) ∨ (¬ p2553) ∨ (¬ p3422) ∨ (¬ p3874))
    : p3641 ∨ (¬ p2470) ∨ (¬ p3422) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h47895 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step77730 (p2707 p2819 p2829 p3688 p4358 p4475 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73564 : p4358 ∨ p2819)
    (h71375 : (¬ p3688) ∨ (¬ p4358) ∨ (¬ p2707) ∨ (¬ p4475))
    : p2829 ∨ (¬ p2707) ∨ (¬ p4475) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71375 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step77732 (p2177 p2717 p3659 p4475 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h20027 : (¬ p2177) ∨ (¬ p3659) ∨ (¬ p4475))
    : (¬ p4475) ∨ p2717 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4475 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h20027 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u0)))))))

theorem step77739 (p2774 p2780 p2819 p3425 p3471 p4358 p4475 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73564 : p4358 ∨ p2819)
    (h73396 : p3471 ∨ p3425)
    (h71376 : (¬ p4358) ∨ (¬ p3471) ∨ (¬ p2780) ∨ (¬ p4475))
    : p2774 ∨ p2819 ∨ (¬ p4475) ∨ p3425 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71376 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step77741 (p2553 p2588 p2598 p3055 p3367 p3425 p3471 p4475 : Prop)
    (h73350 : p3055 ∨ p2598)
    (h73396 : p3471 ∨ p3425)
    (h73282 : p2588 ∨ p2553)
    (h45032 : (¬ p2588) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3471) ∨ (¬ p4475))
    : (¬ p4475) ∨ p2598 ∨ p3425 ∨ (¬ p3367) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4475 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2598) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45032 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step77747 (p2707 p3367 p3389 p3588 p4106 p4730 : Prop)
    (h73430 : p3588 ∨ p2707)
    (h40964 : (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3588) ∨ (¬ p4106) ∨ (¬ p4730))
    : (¬ p3367) ∨ p2707 ∨ (¬ p4730) ∨ (¬ p3389) ∨ (¬ p4106) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4106 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3588 := (Or.elim h73430 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h40964 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step77749 (p2122 p2850 p3093 p3309 p3822 p5220 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h58095 : (¬ p2850) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3822) ∨ (¬ p5220))
    : (¬ p3309) ∨ (¬ p2850) ∨ (¬ p5220) ∨ p2122 ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h58095 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step77753 (p2352 p2819 p3016 p4358 p4750 p5220 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h49411 : (¬ p2352) ∨ (¬ p3016) ∨ (¬ p4358) ∨ (¬ p4750) ∨ (¬ p5220))
    : (¬ p2352) ∨ (¬ p3016) ∨ (¬ p5220) ∨ (¬ p4750) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49411 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step77760 (p2829 p3367 p3585 p5220 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h19800 : (¬ p2829) ∨ (¬ p3585) ∨ (¬ p5220))
    : (¬ p2829) ∨ (¬ p5220) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h19800 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step77762 (p2352 p2819 p2850 p4358 p4715 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h68391 : (¬ p2352) ∨ (¬ p4358) ∨ (¬ p4715) ∨ (¬ p2850))
    : (¬ p2352) ∨ p2819 ∨ (¬ p4715) ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h68391 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step77763 (p2122 p2307 p2498 p2850 p3822 p4715 p5016 p5220 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h50342 : (¬ p2307) ∨ (¬ p2498) ∨ (¬ p2850) ∨ (¬ p3822) ∨ (¬ p4715) ∨ (¬ p5016) ∨ (¬ p5220))
    : p2122 ∨ (¬ p5220) ∨ (¬ p2498) ∨ (¬ p4715) ∨ (¬ p2307) ∨ (¬ p5016) ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p5220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2498 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h50342 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u1)))))))))))))))

theorem step77766 (p2122 p2553 p3641 p3660 p3822 p4610 p5220 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h41607 : (¬ p2553) ∨ (¬ p3641) ∨ (¬ p3660) ∨ (¬ p3822) ∨ (¬ p4610) ∨ (¬ p5220))
    : (¬ p2553) ∨ (¬ p3641) ∨ (¬ p3660) ∨ p2122 ∨ (¬ p5220) ∨ (¬ p4610) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4610 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41607 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step77767 (p2598 p2774 p2780 p3055 p5220 : Prop)
    (h73307 : (¬ p2774) ∨ (¬ p2780))
    (h73350 : p3055 ∨ p2598)
    (h21730 : p2780 ∨ (¬ p3055) ∨ (¬ p5220))
    : (¬ p2774) ∨ (¬ p5220) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2774 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2780) := (Or.elim h73307 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h21730 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u1)))))))

theorem step77770 (p2122 p2553 p2588 p3822 p4342 : Prop)
    (h73471 : (¬ p2122) ∨ (¬ p3822))
    (h73282 : p2588 ∨ p2553)
    (h6589 : (¬ p2588) ∨ p3822 ∨ (¬ p4342))
    : (¬ p2122) ∨ (¬ p4342) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4342 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3822) := (Or.elim h73471 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h6589 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step77772 (p2122 p2274 p3097 p3822 p4428 : Prop)
    (h73471 : (¬ p2122) ∨ (¬ p3822))
    (h73352 : p3097 ∨ p2274)
    (h22468 : (¬ p3097) ∨ p3822 ∨ (¬ p4428))
    : (¬ p2122) ∨ (¬ p4428) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4428 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3822) := (Or.elim h73471 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h22468 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step77774 (p2122 p2819 p3325 p3822 p4358 : Prop)
    (h73471 : (¬ p2122) ∨ (¬ p3822))
    (h73564 : p4358 ∨ p2819)
    (h36960 : (¬ p3325) ∨ p3822 ∨ (¬ p4358))
    : (¬ p2122) ∨ (¬ p3325) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3822) := (Or.elim h73471 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h36960 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step77775 (p2307 p2553 p2584 p2588 p3422 p3584 p4730 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h73282 : p2588 ∨ p2553)
    (h41751 : (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p3584) ∨ (¬ p4730))
    : (¬ p2307) ∨ p3422 ∨ (¬ p4730) ∨ (¬ p2584) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41751 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step77776 (p2156 p2563 p2850 p3684 p4110 p4399 p4730 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73516 : p4110 ∨ p2563)
    (h41066 : (¬ p2156) ∨ (¬ p3684) ∨ (¬ p4110) ∨ (¬ p4399) ∨ (¬ p4730))
    : p2850 ∨ (¬ p2156) ∨ (¬ p4730) ∨ (¬ p4399) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41066 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step77777 (p2427 p2850 p3051 p3684 p4235 p4399 p4730 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73536 : p4235 ∨ p2427)
    (h50885 : (¬ p3051) ∨ (¬ p3684) ∨ (¬ p4235) ∨ (¬ p4399) ∨ (¬ p4730))
    : (¬ p4399) ∨ (¬ p3051) ∨ p2850 ∨ (¬ p4730) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50885 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step77779 (p2220 p2373 p2850 p3684 p3880 p4399 p4730 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73442 : p3684 ∨ p2850)
    (h42627 : (¬ p2220) ∨ (¬ p3684) ∨ (¬ p3880) ∨ (¬ p4399) ∨ (¬ p4730))
    : (¬ p4399) ∨ (¬ p2220) ∨ p2373 ∨ p2850 ∨ (¬ p4730) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42627 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step77780 (p2470 p3367 p3537 p4242 p4730 p5369 : Prop)
    (h73538 : p4242 ∨ p3537)
    (h41843 : (¬ p2470) ∨ (¬ p3367) ∨ (¬ p4242) ∨ (¬ p4730) ∨ (¬ p5369))
    : (¬ p5369) ∨ p3537 ∨ (¬ p3367) ∨ (¬ p2470) ∨ (¬ p4730) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5369 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3537) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4242 := (Or.elim h73538 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41843 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step77781 (p2829 p3367 p3389 p3688 p3689 p4106 p4730 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h41945 : (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3688) ∨ (¬ p3689) ∨ (¬ p4106) ∨ (¬ p4730))
    : (¬ p4106) ∨ (¬ p3689) ∨ (¬ p3389) ∨ (¬ p4730) ∨ p2829 ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4106 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3689 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41945 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step77783 (p2098 p2104 p2598 p3055 p5368 : Prop)
    (h73203 : (¬ p2098) ∨ (¬ p2104))
    (h73350 : p3055 ∨ p2598)
    (h19414 : p2104 ∨ (¬ p3055) ∨ (¬ p5368))
    : (¬ p2098) ∨ (¬ p5368) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2104) := (Or.elim h73203 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h19414 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u1)))))))

theorem step77787 (p2528 p2573 p2579 p3422 p3609 p3905 p4340 p5368 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h73274 : p2579 ∨ p2573)
    (h58824 : (¬ p2528) ∨ (¬ p2579) ∨ (¬ p3422) ∨ (¬ p3905) ∨ (¬ p4340) ∨ (¬ p5368))
    : p3609 ∨ p2573 ∨ (¬ p3905) ∨ (¬ p3422) ∨ (¬ p5368) ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h58824 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step77789 (p2187 p2210 p2528 p3093 p3367 p3555 p3585 p3609 p4340 p4377 p4384 p4516 p5368 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h73412 : p3555 ∨ p2210)
    (h73558 : p4340 ∨ p3609)
    (h48923 : (¬ p2187) ∨ (¬ p2528) ∨ (¬ p3093) ∨ (¬ p3555) ∨ (¬ p3585) ∨ (¬ p4340) ∨ (¬ p4377) ∨ (¬ p4384) ∨ (¬ p4516) ∨ (¬ p5368))
    : (¬ p4516) ∨ (¬ p3093) ∨ (¬ p2187) ∨ p3367 ∨ p2210 ∨ p3609 ∨ (¬ p2528) ∨ (¬ p5368) ∨ (¬ p4377) ∨ (¬ p4384) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4384 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h48923 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step77792 (p2470 p2528 p3609 p4340 p4730 p5368 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h41844 : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p4340) ∨ (¬ p4730) ∨ (¬ p5368))
    : (¬ p2470) ∨ (¬ p5368) ∨ (¬ p2528) ∨ p3609 ∨ (¬ p4730) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41844 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step77793 (p3193 p3222 p3590 p3609 p4340 p4695 p5368 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73558 : p4340 ∨ p3609)
    (h21577 : (¬ p3222) ∨ (¬ p3590) ∨ (¬ p4340) ∨ (¬ p4695) ∨ (¬ p5368))
    : p3193 ∨ p3609 ∨ (¬ p3590) ∨ (¬ p4695) ∨ (¬ p5368) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h21577 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step77841 (p2156 p2192 p2737 p3759 p4173 p4399 p4749 p4874 : Prop)
    (h73528 : p4173 ∨ p2192)
    (h63012 : (¬ p2156) ∨ (¬ p2737) ∨ (¬ p3759) ∨ (¬ p4173) ∨ (¬ p4399) ∨ (¬ p4749) ∨ (¬ p4874))
    : (¬ p2737) ∨ p2192 ∨ (¬ p4749) ∨ (¬ p2156) ∨ (¬ p4399) ∨ (¬ p4874) ∨ (¬ p3759) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2192) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h63012 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step77852 (p2459 p2470 p2528 p3367 p3759 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h46119 : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p4348))
    : (¬ p3367) ∨ (¬ p2470) ∨ p2459 ∨ (¬ p3759) ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46119 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step77853 (p2363 p2470 p2528 p3367 p3759 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h46191 : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p4347))
    : (¬ p3367) ∨ p2363 ∨ (¬ p2528) ∨ (¬ p3759) ∨ (¬ p2470) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46191 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step77862 (p2230 p2563 p2737 p2743 p3367 p3759 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h45801 : (¬ p2230) ∨ (¬ p2563) ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3759))
    : p2737 ∨ (¬ p3367) ∨ (¬ p2230) ∨ (¬ p3759) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45801 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step77876 (p2230 p2440 p2737 p2743 p3367 p3759 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h45946 : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3759))
    : (¬ p3759) ∨ (¬ p2230) ∨ (¬ p2440) ∨ p2737 ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3759 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45946 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step77882 (p2440 p2542 p2573 p3016 p3367 p3574 p3759 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73422 : p3574 ∨ p3016)
    (h61741 : (¬ p2542) ∨ (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3574) ∨ (¬ p3759))
    : (¬ p3367) ∨ (¬ p3759) ∨ p2440 ∨ p3016 ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61741 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step77890 (p2307 p2352 p2553 p2584 p2588 p3367 p3759 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h55071 : (¬ p2307) ∨ (¬ p2352) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p3367) ∨ (¬ p3759))
    : (¬ p2307) ∨ (¬ p3759) ∨ (¬ p2352) ∨ (¬ p3367) ∨ (¬ p2584) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h55071 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step77894 (p2417 p2437 p2662 p2737 p2743 p3367 p3759 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h53954 : (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2662) ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3759))
    : (¬ p3367) ∨ p2737 ∨ (¬ p2662) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p3759) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h53954 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step77898 (p2573 p3201 p3759 p3876 p3920 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h25616 : (¬ p2573) ∨ (¬ p3759) ∨ (¬ p3876) ∨ (¬ p3920))
    : p3201 ∨ (¬ p3920) ∨ (¬ p2573) ∨ (¬ p3759) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p3920 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h25616 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step77903 (p2352 p2573 p2737 p2743 p3367 p3759 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h61830 : (¬ p2352) ∨ (¬ p2573) ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3759))
    : (¬ p3367) ∨ (¬ p2352) ∨ (¬ p2573) ∨ p2737 ∨ (¬ p3759) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61830 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step77905 (p2553 p2573 p2737 p2743 p3367 p3759 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h45803 : (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3759))
    : p2737 ∨ (¬ p3759) ∨ (¬ p3367) ∨ (¬ p2553) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45803 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step77906 (p2573 p3422 p3584 p3759 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h5512 : (¬ p2573) ∨ (¬ p3584) ∨ (¬ p3759))
    : p3422 ∨ (¬ p3759) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h5512 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step77907 (p2470 p2476 p3641 p3759 p3874 : Prop)
    (h73249 : (¬ p2470) ∨ (¬ p2476))
    (h73484 : p3874 ∨ p3641)
    (h39666 : p2476 ∨ (¬ p3759) ∨ (¬ p3874))
    : (¬ p2470) ∨ p3641 ∨ (¬ p3759) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2476) := (Or.elim h73249 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h39666 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u4)))))))

theorem step77913 (p2737 p2743 p3276 p3355 p3367 p3759 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h61519 : (¬ p2743) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3367) ∨ (¬ p3759))
    : p2737 ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p3276) ∨ (¬ p3355) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h61519 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step77941 (p2220 p2373 p2563 p3367 p3759 p3880 p4399 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h43904 : (¬ p2220) ∨ (¬ p2563) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p3880) ∨ (¬ p4399))
    : (¬ p3367) ∨ (¬ p2220) ∨ (¬ p3759) ∨ (¬ p2563) ∨ p2373 ∨ (¬ p4399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43904 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step77952 (p2717 p4804 p5909 : Prop)
    (h74219 : (¬ p2717) ∨ (¬ p5909))
    (h12436 : p4804 ∨ p5909)
    : p4804 ∨ (¬ p2717) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4804) := (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5909) := (Or.elim h74219 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12436 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step77953 (p2717 p4805 p5909 : Prop)
    (h74219 : (¬ p2717) ∨ (¬ p5909))
    (h12437 : p4805 ∨ p5909)
    : p4805 ∨ (¬ p2717) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4805) := (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5909) := (Or.elim h74219 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12437 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step77954 (p2717 p4806 p5909 : Prop)
    (h74219 : (¬ p2717) ∨ (¬ p5909))
    (h12439 : p4806 ∨ p5909)
    : p4806 ∨ (¬ p2717) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4806) := (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5909) := (Or.elim h74219 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12439 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step77955 (p2717 p4807 p5909 : Prop)
    (h74219 : (¬ p2717) ∨ (¬ p5909))
    (h12440 : p4807 ∨ p5909)
    : p4807 ∨ (¬ p2717) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4807) := (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5909) := (Or.elim h74219 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12440 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step77956 (p2274 p4140 p4557 : Prop)
    (h73636 : p4557 ∨ (¬ p2274))
    (h7206 : p4140 ∨ (¬ p4557))
    : p4140 ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4140) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h7206 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step77958 (p2274 p4557 p4558 : Prop)
    (h73636 : p4557 ∨ (¬ p2274))
    (h7209 : (¬ p4557) ∨ p4558)
    : (¬ p2274) ∨ p4558 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4558) := (fun h => hn (Or.inr h));
    let u2 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h7209 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step77959 (p2274 p4557 p4559 : Prop)
    (h73636 : p4557 ∨ (¬ p2274))
    (h7210 : (¬ p4557) ∨ p4559)
    : (¬ p2274) ∨ p4559 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4559) := (fun h => hn (Or.inr h));
    let u2 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h7210 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step77961 (p2284 p3745 p4562 : Prop)
    (h73638 : p4562 ∨ p2284)
    (h7219 : p3745 ∨ (¬ p4562))
    : p3745 ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3745) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr h));
    let u2 : p4562 := (Or.elim h73638 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h7219 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step77962 (p2284 p4562 p4563 : Prop)
    (h73638 : p4562 ∨ p2284)
    (h7221 : (¬ p4562) ∨ p4563)
    : p2284 ∨ p4563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2284) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4563) := (fun h => hn (Or.inr h));
    let u2 : p4562 := (Or.elim h73638 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7221 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step77963 (p2284 p4562 p4564 : Prop)
    (h73638 : p4562 ∨ p2284)
    (h7222 : (¬ p4562) ∨ p4564)
    : p2284 ∨ p4564 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2284) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4564) := (fun h => hn (Or.inr h));
    let u2 : p4562 := (Or.elim h73638 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7222 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step77964 (p2284 p2563 p2737 p2743 p2946 p2952 p3361 p3952 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73496 : p3952 ∨ p2284)
    (h73298 : p2743 ∨ p2737)
    (h43006 : (¬ p2563) ∨ (¬ p2743) ∨ (¬ p2952) ∨ (¬ p3361) ∨ (¬ p3952))
    : p2946 ∨ p2284 ∨ p2737 ∨ (¬ p3361) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43006 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step77965 (p2156 p2254 p2284 p2946 p2952 p3952 p4172 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73496 : p3952 ∨ p2284)
    (h41018 : (¬ p2156) ∨ (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3952) ∨ (¬ p4172))
    : p2946 ∨ p2284 ∨ (¬ p2156) ∨ (¬ p4172) ∨ (¬ p2254) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41018 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step77966 (p2187 p2284 p2901 p3952 p3989 p4140 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73502 : p3989 ∨ p2187)
    (h71382 : (¬ p3989) ∨ (¬ p3952) ∨ (¬ p2901) ∨ (¬ p4140))
    : (¬ p2901) ∨ p2284 ∨ p2187 ∨ (¬ p4140) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h71382 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step77967 (p2284 p2427 p2563 p2946 p2952 p3952 p4235 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73496 : p3952 ∨ p2284)
    (h73330 : p2952 ∨ p2946)
    (h49776 : (¬ p2563) ∨ (¬ p2952) ∨ (¬ p3952) ∨ (¬ p4235))
    : p2427 ∨ p2284 ∨ (¬ p2563) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2427) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49776 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step77969 (p2187 p2284 p2383 p2960 p2962 p3952 p3989 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73502 : p3989 ∨ p2187)
    (h48347 : (¬ p2383) ∨ (¬ p2960) ∨ (¬ p2962) ∨ (¬ p3952) ∨ (¬ p3989))
    : (¬ p2383) ∨ p2284 ∨ p2187 ∨ (¬ p2960) ∨ (¬ p2962) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48347 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step77970 (p2177 p2274 p2284 p2299 p2946 p2952 p3097 p3952 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73330 : p2952 ∨ p2946)
    (h73352 : p3097 ∨ p2274)
    (h73234 : p2299 ∨ p2177)
    (h45296 : (¬ p2299) ∨ (¬ p2952) ∨ (¬ p3097) ∨ (¬ p3952))
    : p2284 ∨ p2946 ∨ p2274 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2284) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45296 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step77972 (p2274 p2284 p2396 p2946 p2952 p3097 p3952 p4107 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73496 : p3952 ∨ p2284)
    (h73330 : p2952 ∨ p2946)
    (h73352 : p3097 ∨ p2274)
    (h45302 : (¬ p2952) ∨ (¬ p3097) ∨ (¬ p3952) ∨ (¬ p4107))
    : p2396 ∨ p2284 ∨ p2946 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2396) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45302 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step77973 (p2192 p2249 p2284 p2946 p2952 p3952 p4365 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73496 : p3952 ∨ p2284)
    (h51761 : (¬ p2192) ∨ (¬ p2249) ∨ (¬ p2952) ∨ (¬ p3952) ∨ (¬ p4365))
    : (¬ p4365) ∨ p2946 ∨ p2284 ∨ (¬ p2192) ∨ (¬ p2249) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4365 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h51761 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step77974 (p2187 p2284 p3063 p3309 p3549 p3952 p3989 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h73496 : p3952 ∨ p2284)
    (h73502 : p3989 ∨ p2187)
    (h47409 : (¬ p3063) ∨ (¬ p3549) ∨ (¬ p3952) ∨ (¬ p3989))
    : (¬ p3063) ∨ p3309 ∨ p2284 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3309) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47409 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step77975 (p2274 p2284 p2946 p2952 p3097 p3166 p3952 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73496 : p3952 ∨ p2284)
    (h73352 : p3097 ∨ p2274)
    (h43448 : (¬ p2952) ∨ (¬ p3097) ∨ (¬ p3166) ∨ (¬ p3952))
    : (¬ p3166) ∨ p2946 ∨ p2284 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43448 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step77976 (p2187 p2284 p2651 p2946 p2952 p3952 p3989 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73496 : p3952 ∨ p2284)
    (h73502 : p3989 ∨ p2187)
    (h44330 : (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3952) ∨ (¬ p3989))
    : p2946 ∨ p2284 ∨ (¬ p2651) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44330 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step77977 (p2187 p2284 p2363 p2946 p2952 p3952 p3989 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73330 : p2952 ∨ p2946)
    (h73502 : p3989 ∨ p2187)
    (h73496 : p3952 ∨ p2284)
    (h42842 : (¬ p2952) ∨ (¬ p3952) ∨ (¬ p3989) ∨ (¬ p4347))
    : p2363 ∨ p2946 ∨ p2187 ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42842 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step77980 (p2252 p2284 p2608 p2750 p2946 p2952 p3125 p3399 p3631 p3744 p3952 p3954 p4625 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73454 : p3744 ∨ p3125)
    (h73330 : p2952 ∨ p2946)
    (h73496 : p3952 ∨ p2284)
    (h41593 : (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p3954) ∨ (¬ p4625))
    : (¬ p3631) ∨ p2608 ∨ p3125 ∨ p2946 ∨ p2284 ∨ (¬ p3399) ∨ (¬ p2750) ∨ (¬ p4625) ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41593 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step77981 (p2254 p2284 p2459 p2946 p2952 p3125 p3399 p3527 p3744 p3952 p4604 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h73496 : p3952 ∨ p2284)
    (h73330 : p2952 ∨ p2946)
    (h41243 : (¬ p2254) ∨ (¬ p2459) ∨ (¬ p2952) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p4604))
    : (¬ p3527) ∨ p3125 ∨ p2284 ∨ (¬ p2254) ∨ (¬ p4604) ∨ (¬ p3399) ∨ (¬ p2459) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h41243 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step77982 (p2187 p2284 p2737 p2743 p2946 p2952 p3361 p3952 p3989 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73330 : p2952 ∨ p2946)
    (h73298 : p2743 ∨ p2737)
    (h73502 : p3989 ∨ p2187)
    (h45623 : (¬ p2743) ∨ (¬ p2952) ∨ (¬ p3361) ∨ (¬ p3952) ∨ (¬ p3989))
    : p2284 ∨ p2946 ∨ (¬ p3361) ∨ p2737 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2284) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45623 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u8)))))))))))

theorem step77985 (p2122 p2187 p2254 p2284 p2608 p2829 p2946 p2952 p3952 p3989 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73502 : p3989 ∨ p2187)
    (h73496 : p3952 ∨ p2284)
    (h71383 : (¬ p2829) ∨ (¬ p2608) ∨ (¬ p2122) ∨ (¬ p3952) ∨ (¬ p2254) ∨ (¬ p3989) ∨ (¬ p2952))
    : (¬ p2829) ∨ p2946 ∨ p2187 ∨ p2284 ∨ (¬ p2254) ∨ (¬ p2122) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71383 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (False.elim (r5 u7)))))))))))))))

theorem step77986 (p2284 p2860 p2946 p2952 p3952 p4313 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73496 : p3952 ∨ p2284)
    (h71384 : (¬ p2860) ∨ (¬ p4313) ∨ (¬ p3952) ∨ (¬ p2952))
    : p2946 ∨ p2284 ∨ (¬ p2860) ∨ (¬ p4313) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71384 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step77988 (p2284 p2563 p2651 p2946 p2952 p3952 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73496 : p3952 ∨ p2284)
    (h42733 : (¬ p2563) ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3952))
    : p2946 ∨ p2284 ∨ (¬ p2651) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42733 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step77990 (p2274 p2284 p2651 p2946 p2952 p3097 p3952 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73352 : p3097 ∨ p2274)
    (h73496 : p3952 ∨ p2284)
    (h60300 : (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3097) ∨ (¬ p3952))
    : p2946 ∨ p2274 ∨ p2284 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h60300 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step77992 (p2187 p2254 p2284 p2608 p2707 p2717 p2946 p2952 p3952 p3989 p4503 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73502 : p3989 ∨ p2187)
    (h73496 : p3952 ∨ p2284)
    (h54060 : (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p2952) ∨ (¬ p3952) ∨ (¬ p3989) ∨ (¬ p4503))
    : (¬ p2707) ∨ (¬ p2717) ∨ (¬ p4503) ∨ p2946 ∨ p2187 ∨ (¬ p2608) ∨ p2284 ∨ (¬ p2254) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h54060 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step77993 (p2284 p2651 p2727 p2946 p2952 p3952 p4111 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73518 : p4111 ∨ p2727)
    (h73496 : p3952 ∨ p2284)
    (h42672 : (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3952) ∨ (¬ p4111))
    : (¬ p2651) ∨ p2946 ∨ p2727 ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42672 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step77994 (p2156 p2284 p2528 p2534 p2598 p2958 p3055 p3115 p3641 p3874 p3952 p4450 p4786 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73350 : p3055 ∨ p2598)
    (h73484 : p3874 ∨ p3641)
    (h73268 : p2534 ∨ p2528)
    (h57487 : (¬ p2156) ∨ (¬ p2534) ∨ (¬ p2958) ∨ (¬ p3055) ∨ (¬ p3115) ∨ (¬ p3874) ∨ (¬ p3952) ∨ (¬ p4450) ∨ (¬ p4786))
    : (¬ p2958) ∨ p2284 ∨ p2598 ∨ p3641 ∨ (¬ p4450) ∨ (¬ p3115) ∨ (¬ p4786) ∨ (¬ p2156) ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2958 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h57487 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step77996 (p2187 p2284 p2352 p2553 p2588 p3952 p3989 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73496 : p3952 ∨ p2284)
    (h73502 : p3989 ∨ p2187)
    (h62260 : (¬ p2352) ∨ (¬ p2588) ∨ (¬ p3952) ∨ (¬ p3989))
    : (¬ p2352) ∨ p2553 ∨ p2284 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62260 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step77997 (p2274 p2284 p3097 p3156 p3952 p4405 p4441 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73352 : p3097 ∨ p2274)
    (h53186 : (¬ p3097) ∨ (¬ p3156) ∨ (¬ p3952) ∨ (¬ p4405) ∨ (¬ p4441))
    : (¬ p3156) ∨ p2284 ∨ p2274 ∨ (¬ p4405) ∨ (¬ p4441) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h53186 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step77999 (p2563 p3096 p4714 : Prop)
    (h73720 : p4714 ∨ p2563)
    (h7617 : p3096 ∨ (¬ p4714))
    : p3096 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3096) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr h));
    let u2 : p4714 := (Or.elim h73720 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h7617 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step78000 (p2563 p4714 p4715 : Prop)
    (h73720 : p4714 ∨ p2563)
    (h7619 : (¬ p4714) ∨ p4715)
    : p2563 ∨ p4715 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2563) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4715) := (fun h => hn (Or.inr h));
    let u2 : p4714 := (Or.elim h73720 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7619 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step78001 (p2563 p3958 p4714 : Prop)
    (h73720 : p4714 ∨ p2563)
    (h7620 : p3958 ∨ (¬ p4714))
    : p3958 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3958) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr h));
    let u2 : p4714 := (Or.elim h73720 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h7620 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step78002 (p2563 p4110 p4555 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h42928 : (¬ p4110) ∨ p4555)
    : p2563 ∨ p4555 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2563) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4555) := (fun h => hn (Or.inr h));
    let u2 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42928 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step78003 (p2563 p4110 p4702 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h44622 : (¬ p4110) ∨ p4702)
    : p2563 ∨ p4702 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2563) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4702) := (fun h => hn (Or.inr h));
    let u2 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h44622 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step78004 (p2563 p4110 p4718 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h46647 : (¬ p4110) ∨ p4718)
    : p2563 ∨ p4718 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2563) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4718) := (fun h => hn (Or.inr h));
    let u2 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h46647 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step78005 (p2563 p4110 p4646 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h47642 : (¬ p4110) ∨ p4646)
    : p2563 ∨ p4646 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2563) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4646) := (fun h => hn (Or.inr h));
    let u2 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h47642 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step78006 (p2187 p2363 p2563 p3266 p3989 p4110 p4347 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73560 : p4347 ∨ p2363)
    (h73516 : p4110 ∨ p2563)
    (h73502 : p3989 ∨ p2187)
    (h43794 : (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4347) ∨ (¬ p4444))
    : p3266 ∨ p2363 ∨ p2563 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43794 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78007 (p2187 p2230 p2363 p2563 p2589 p3989 p4110 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73516 : p4110 ∨ p2563)
    (h73502 : p3989 ∨ p2187)
    (h73284 : p2589 ∨ p2230)
    (h42759 : (¬ p2589) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4347))
    : p2363 ∨ p2563 ∨ p2187 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42759 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78008 (p2187 p2427 p2563 p3989 p4110 p4140 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h73516 : p4110 ∨ p2563)
    (h71387 : (¬ p3989) ∨ (¬ p2427) ∨ (¬ p4110) ∨ (¬ p4140))
    : (¬ p2427) ∨ (¬ p4140) ∨ p2187 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71387 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step78010 (p2187 p2440 p2563 p2651 p2657 p3989 p4110 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73516 : p4110 ∨ p2563)
    (h73502 : p3989 ∨ p2187)
    (h42995 : (¬ p2440) ∨ (¬ p2657) ∨ (¬ p3989) ∨ (¬ p4110))
    : (¬ p2440) ∨ p2651 ∨ p2563 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42995 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step78011 (p2284 p2427 p2563 p2651 p3413 p4110 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h42856 : (¬ p2284) ∨ (¬ p2427) ∨ (¬ p2651) ∨ (¬ p3413) ∨ (¬ p4110))
    : (¬ p2284) ∨ (¬ p2651) ∨ (¬ p2427) ∨ p2563 ∨ (¬ p3413) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42856 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78018 (p2230 p2363 p2563 p2589 p3146 p3692 p3988 p4110 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73284 : p2589 ∨ p2230)
    (h73516 : p4110 ∨ p2563)
    (h49147 : (¬ p2363) ∨ (¬ p2589) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4110))
    : p3146 ∨ (¬ p2363) ∨ p2230 ∨ p2563 ∨ (¬ p3988) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49147 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step78019 (p2187 p2563 p2839 p3367 p3583 p3698 p3989 p4110 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73516 : p4110 ∨ p2563)
    (h73502 : p3989 ∨ p2187)
    (h44329 : (¬ p3367) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p3989) ∨ (¬ p4110))
    : (¬ p3367) ∨ p2839 ∨ p2563 ∨ (¬ p3698) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h44329 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step78021 (p2187 p2563 p2651 p2946 p2952 p3879 p3989 p4110 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73516 : p4110 ∨ p2563)
    (h73502 : p3989 ∨ p2187)
    (h48380 : (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3879) ∨ (¬ p3989) ∨ (¬ p4110))
    : p2946 ∨ (¬ p3879) ∨ p2563 ∨ (¬ p2651) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48380 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step78025 (p2331 p2563 p2946 p2952 p3986 p4110 p4705 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73516 : p4110 ∨ p2563)
    (h42040 : (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3986) ∨ (¬ p4110) ∨ (¬ p4705))
    : (¬ p2331) ∨ p2946 ∨ (¬ p4705) ∨ p2563 ∨ (¬ p3986) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42040 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step78026 (p2187 p2331 p2563 p2668 p3989 p4110 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h73502 : p3989 ∨ p2187)
    (h59219 : (¬ p2331) ∨ (¬ p2668) ∨ (¬ p3989) ∨ (¬ p4110))
    : (¬ p2331) ∨ (¬ p2668) ∨ p2563 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h59219 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78028 (p2563 p2946 p2952 p3166 p3189 p3879 p4110 p4360 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73516 : p4110 ∨ p2563)
    (h73566 : p4360 ∨ p3189)
    (h64056 : (¬ p2952) ∨ (¬ p3166) ∨ (¬ p3879) ∨ (¬ p4110) ∨ (¬ p4360))
    : (¬ p3166) ∨ p2946 ∨ p2563 ∨ p3189 ∨ (¬ p3879) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h64056 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step78030 (p2187 p2307 p2313 p2383 p2563 p3989 p4110 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73502 : p3989 ∨ p2187)
    (h73516 : p4110 ∨ p2563)
    (h45292 : (¬ p2313) ∨ (¬ p2383) ∨ (¬ p3989) ∨ (¬ p4110))
    : (¬ p2383) ∨ p2307 ∨ p2187 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45292 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step78031 (p2187 p2295 p2563 p2668 p3568 p3989 p4110 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73502 : p3989 ∨ p2187)
    (h73516 : p4110 ∨ p2563)
    (h45273 : (¬ p2668) ∨ (¬ p3568) ∨ (¬ p3989) ∨ (¬ p4110))
    : (¬ p2668) ∨ p2295 ∨ p2187 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45273 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step78034 (p2139 p2177 p2299 p2437 p2630 p2696 p2810 p2881 p3051 p3365 p3742 p4712 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h73452 : p3742 ∨ p2437)
    (h73390 : p3365 ∨ p2696)
    (h73316 : p2810 ∨ p2630)
    (h51156 : (¬ p2139) ∨ (¬ p2299) ∨ (¬ p2810) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3365) ∨ (¬ p3742) ∨ (¬ p4712))
    : (¬ p3051) ∨ (¬ p2881) ∨ p2177 ∨ (¬ p4712) ∨ p2437 ∨ (¬ p2139) ∨ p2696 ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h51156 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step78037 (p2122 p2177 p2299 p2774 p2780 p2881 p3822 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73308 : p2780 ∨ p2774)
    (h73234 : p2299 ∨ p2177)
    (h43687 : (¬ p2299) ∨ (¬ p2780) ∨ (¬ p2881) ∨ (¬ p3822))
    : (¬ p2881) ∨ p2122 ∨ p2774 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43687 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78038 (p2132 p2363 p2470 p2476 p2528 p2534 p2750 p2753 p2870 p2881 p3347 p3402 p4503 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73250 : p2476 ∨ p2470)
    (h54149 : (¬ p2132) ∨ (¬ p2363) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3347) ∨ (¬ p3402) ∨ (¬ p4503))
    : p2528 ∨ (¬ p2753) ∨ (¬ p2881) ∨ p2470 ∨ (¬ p3347) ∨ (¬ p2363) ∨ (¬ p3402) ∨ (¬ p2870) ∨ (¬ p2750) ∨ (¬ p2132) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54149 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (False.elim (r9 u10)))))))))))))))))))))))

theorem step78039 (p2177 p2299 p2417 p2881 p3246 p3690 p4712 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73234 : p2299 ∨ p2177)
    (h64490 : (¬ p2299) ∨ (¬ p2417) ∨ (¬ p2881) ∨ (¬ p3690) ∨ (¬ p4712))
    : (¬ p2417) ∨ p3246 ∨ (¬ p2881) ∨ p2177 ∨ (¬ p4712) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h64490 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step78040 (p2177 p2299 p2881 p4275 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h20042 : (¬ p2299) ∨ (¬ p2881) ∨ (¬ p4275))
    : (¬ p2881) ∨ (¬ p4275) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20042 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step78046 (p2177 p2299 p2553 p2588 p2881 p3872 p3958 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73234 : p2299 ∨ p2177)
    (h51714 : (¬ p2299) ∨ (¬ p2588) ∨ (¬ p2881) ∨ (¬ p3872) ∨ (¬ p3958))
    : (¬ p2881) ∨ p2553 ∨ (¬ p3872) ∨ (¬ p3958) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51714 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step78048 (p2177 p2284 p2299 p2881 p2946 p3872 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h43513 : (¬ p2284) ∨ (¬ p2299) ∨ (¬ p2881) ∨ (¬ p2946) ∨ (¬ p3872))
    : (¬ p2881) ∨ (¬ p2284) ∨ p2177 ∨ (¬ p2946) ∨ (¬ p3872) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43513 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step78052 (p2396 p2427 p2563 p3246 p4107 p4110 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73516 : p4110 ∨ p2563)
    (h50305 : (¬ p2427) ∨ (¬ p3246) ∨ (¬ p4107) ∨ (¬ p4110))
    : (¬ p3246) ∨ p2396 ∨ p2563 ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50305 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step78055 (p2881 p3246 p3570 p3657 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h20115 : (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3657))
    : (¬ p3246) ∨ (¬ p3657) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20115 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step78061 (p2417 p2437 p2881 p3246 p3570 p3742 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73452 : p3742 ∨ p2437)
    (h73418 : p3570 ∨ p2881)
    (h55107 : (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3742) ∨ (¬ p4278))
    : p2417 ∨ (¬ p3246) ∨ p2437 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55107 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78064 (p2406 p2881 p3238 p3246 p3516 p3570 p3821 p4031 p4257 p4984 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73418 : p3570 ∨ p2881)
    (h73374 : p3238 ∨ p2406)
    (h63164 : (¬ p3238) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3821) ∨ (¬ p4031) ∨ (¬ p4257) ∨ (¬ p4984))
    : (¬ p3246) ∨ p3516 ∨ p2881 ∨ p2406 ∨ (¬ p4257) ∨ (¬ p4031) ∨ (¬ p4984) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3516) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63164 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step78065 (p2177 p2315 p2881 p3246 p3516 p3570 p3821 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73418 : p3570 ∨ p2881)
    (h61247 : (¬ p2177) ∨ (¬ p2315) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3821))
    : p3516 ∨ (¬ p3246) ∨ (¬ p2315) ∨ p2881 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61247 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78066 (p2717 p2881 p3246 p3425 p3471 p3570 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73396 : p3471 ∨ p3425)
    (h52614 : (¬ p2717) ∨ (¬ p3246) ∨ (¬ p3471) ∨ (¬ p3570))
    : (¬ p3246) ∨ (¬ p2717) ∨ p2881 ∨ p3425 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h52614 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78073 (p2210 p2881 p3246 p3527 p3570 p4431 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h55645 : (¬ p2210) ∨ (¬ p3246) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p4431))
    : (¬ p3246) ∨ (¬ p3527) ∨ (¬ p2210) ∨ p2881 ∨ (¬ p4431) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55645 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step78074 (p2210 p2396 p2891 p3246 p4107 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h50507 : (¬ p2210) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p4107))
    : (¬ p3246) ∨ p2396 ∨ (¬ p2891) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h50507 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78075 (p2396 p3246 p4107 p4275 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h19786 : (¬ p3246) ∨ (¬ p4107) ∨ (¬ p4275))
    : (¬ p3246) ∨ p2396 ∨ (¬ p4275) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h19786 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step78077 (p2881 p3246 p3399 p3527 p3570 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h43127 : (¬ p3246) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3570))
    : (¬ p3246) ∨ (¬ p3527) ∨ p2881 ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43127 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78079 (p2210 p2254 p2528 p2534 p2651 p2657 p2891 p3083 p3246 p3950 p4256 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73288 : p2657 ∨ p2651)
    (h73542 : p4256 ∨ p3083)
    (h48900 : (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p4256))
    : p2528 ∨ (¬ p3246) ∨ (¬ p3950) ∨ p2651 ∨ (¬ p2210) ∨ p3083 ∨ (¬ p2891) ∨ (¬ p2254) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h48900 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u10)))))))))))))))))

theorem step78081 (p2248 p2509 p2528 p2534 p2901 p2946 p3246 p3379 p3452 p3950 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73394 : p3452 ∨ p3379)
    (h48889 : (¬ p2248) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3452) ∨ (¬ p3950))
    : p2528 ∨ (¬ p3950) ∨ (¬ p2901) ∨ (¬ p2248) ∨ p3379 ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p2509) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48889 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step78083 (p2264 p2449 p2881 p3246 p3570 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h31484 : (¬ p2264) ∨ p2449 ∨ (¬ p3246) ∨ (¬ p3570))
    : p2449 ∨ (¬ p3246) ∨ p2881 ∨ (¬ p2264) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h31484 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78088 (p2177 p2299 p2341 p3246 p3516 p3821 p4559 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73234 : p2299 ∨ p2177)
    (h64188 : (¬ p2299) ∨ (¬ p2341) ∨ (¬ p3246) ∨ (¬ p3821) ∨ (¬ p4559))
    : p3516 ∨ (¬ p2341) ∨ (¬ p3246) ∨ p2177 ∨ (¬ p4559) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h64188 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step78089 (p2248 p2901 p2911 p2922 p2928 p2946 p3246 p3379 p3452 p3644 p4668 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73434 : p3644 ∨ p2911)
    (h73320 : p2928 ∨ p2922)
    (h49946 : (¬ p2248) ∨ (¬ p2901) ∨ (¬ p2928) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3452) ∨ (¬ p3644) ∨ (¬ p4668))
    : (¬ p3246) ∨ p3379 ∨ p2911 ∨ (¬ p4668) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p2248) ∨ p2922 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h49946 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step78092 (p2528 p2534 p2598 p2901 p2946 p3055 p3246 p3641 p3874 p3950 p4786 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73484 : p3874 ∨ p3641)
    (h73350 : p3055 ∨ p2598)
    (h52231 : (¬ p2534) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3246) ∨ (¬ p3874) ∨ (¬ p3950) ∨ (¬ p4786))
    : p2528 ∨ (¬ p3246) ∨ (¬ p2901) ∨ (¬ p3950) ∨ (¬ p4786) ∨ p3641 ∨ (¬ p2946) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h52231 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step78093 (p2246 p2598 p2744 p2901 p2911 p2946 p3055 p3201 p3246 p3366 p3644 p3876 p4668 : Prop)
    (h73350 : p3055 ∨ p2598)
    (h73486 : p3876 ∨ p3201)
    (h73434 : p3644 ∨ p2911)
    (h52833 : (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3246) ∨ (¬ p3366) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4668))
    : (¬ p3246) ∨ (¬ p2946) ∨ p2598 ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p4668) ∨ (¬ p3366) ∨ (¬ p2901) ∨ p3201 ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u12 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h52833 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step78096 (p2210 p2598 p2891 p2911 p3055 p3201 p3246 p3644 p3876 p4668 p4736 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73434 : p3644 ∨ p2911)
    (h73350 : p3055 ∨ p2598)
    (h49635 : (¬ p2210) ∨ (¬ p2891) ∨ (¬ p3055) ∨ (¬ p3246) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4668) ∨ (¬ p4736))
    : (¬ p3246) ∨ p3201 ∨ (¬ p4736) ∨ (¬ p4668) ∨ p2911 ∨ (¬ p2210) ∨ (¬ p2891) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h49635 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step78098 (p2210 p2352 p2363 p2573 p2579 p2891 p3246 p3950 p3956 p4347 p5193 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73560 : p4347 ∨ p2363)
    (h73500 : p3956 ∨ p2352)
    (h58687 : (¬ p2210) ∨ (¬ p2579) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p5193))
    : p2573 ∨ p2363 ∨ (¬ p2210) ∨ (¬ p5193) ∨ (¬ p2891) ∨ p2352 ∨ (¬ p3950) ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h58687 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step78099 (p2284 p2396 p2870 p3246 p3952 p4107 p4316 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73496 : p3952 ∨ p2284)
    (h55576 : (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3952) ∨ (¬ p4107) ∨ (¬ p4316))
    : (¬ p3246) ∨ p2396 ∨ (¬ p4316) ∨ p2284 ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55576 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step78100 (p2284 p2396 p2951 p3051 p3246 p3952 p4107 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73496 : p3952 ∨ p2284)
    (h43133 : (¬ p2951) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3952) ∨ (¬ p4107))
    : (¬ p3246) ∨ p2396 ∨ (¬ p2951) ∨ (¬ p3051) ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43133 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78101 (p3125 p3246 p3744 p3872 p4396 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h33875 : (¬ p3246) ∨ (¬ p3744) ∨ (¬ p3872) ∨ (¬ p4396))
    : p3125 ∨ (¬ p3246) ∨ (¬ p4396) ∨ (¬ p3872) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3125) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h33875 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step78103 (p2187 p2383 p2396 p3246 p3872 p3989 p4107 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73502 : p3989 ∨ p2187)
    (h46883 : (¬ p2383) ∨ (¬ p3246) ∨ (¬ p3872) ∨ (¬ p3989) ∨ (¬ p4107))
    : (¬ p3872) ∨ (¬ p3246) ∨ p2396 ∨ (¬ p2383) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3872 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46883 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78105 (p2396 p2553 p2588 p3246 p3872 p3958 p4107 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73282 : p2588 ∨ p2553)
    (h49276 : (¬ p2588) ∨ (¬ p3246) ∨ (¬ p3872) ∨ (¬ p3958) ∨ (¬ p4107))
    : (¬ p3246) ∨ p2396 ∨ (¬ p3958) ∨ p2553 ∨ (¬ p3872) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49276 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78108 (p3246 p5103 p5104 : Prop)
    (h73920 : p5103 ∨ (¬ p3246))
    (h8616 : (¬ p5103) ∨ p5104)
    : (¬ p3246) ∨ p5104 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5104) := (fun h => hn (Or.inr h));
    let u2 : p5103 := (Or.elim h73920 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h8616 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step78109 (p3246 p3951 p5103 : Prop)
    (h73920 : p5103 ∨ (¬ p3246))
    (h8617 : p3951 ∨ (¬ p5103))
    : p3951 ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3951) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5103 := (Or.elim h73920 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h8617 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step78110 (p2901 p4320 p4957 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h45674 : (¬ p4320) ∨ p4957)
    : p2901 ∨ p4957 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4957) := (fun h => hn (Or.inr h));
    let u2 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45674 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step78113 (p2651 p2901 p2946 p2952 p3051 p4320 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73552 : p4320 ∨ p2901)
    (h60542 : (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3051) ∨ (¬ p4320))
    : p2946 ∨ p2901 ∨ (¬ p3051) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h60542 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step78115 (p2254 p2608 p2829 p2901 p2946 p2952 p3246 p3483 p3690 p4320 p4621 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73446 : p3690 ∨ p3246)
    (h73552 : p4320 ∨ p2901)
    (h49305 : (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2829) ∨ (¬ p2952) ∨ (¬ p3483) ∨ (¬ p3690) ∨ (¬ p4320) ∨ (¬ p4621))
    : (¬ p3483) ∨ (¬ p2829) ∨ p2946 ∨ p3246 ∨ (¬ p2608) ∨ (¬ p2254) ∨ (¬ p4621) ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h49305 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step78122 (p2177 p2881 p2901 p2946 p2952 p3570 p4320 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73330 : p2952 ∨ p2946)
    (h73552 : p4320 ∨ p2901)
    (h45272 : (¬ p2177) ∨ (¬ p2952) ∨ (¬ p3570) ∨ (¬ p4320))
    : p2881 ∨ (¬ p2177) ∨ p2946 ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45272 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step78123 (p2177 p2284 p2881 p2901 p3570 p4320 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73418 : p3570 ∨ p2881)
    (h63601 : (¬ p2177) ∨ (¬ p2284) ∨ (¬ p3570) ∨ (¬ p4320))
    : p2901 ∨ (¬ p2284) ∨ (¬ p2177) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63601 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78124 (p2881 p2901 p3527 p3570 p4320 p4431 p4960 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73418 : p3570 ∨ p2881)
    (h50139 : (¬ p3527) ∨ (¬ p3570) ∨ (¬ p4320) ∨ (¬ p4431) ∨ (¬ p4960))
    : (¬ p3527) ∨ p2901 ∨ (¬ p4960) ∨ (¬ p4431) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50139 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step78126 (p2284 p2563 p2901 p3051 p4110 p4320 p4539 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73516 : p4110 ∨ p2563)
    (h41358 : (¬ p2284) ∨ (¬ p3051) ∨ (¬ p4110) ∨ (¬ p4320) ∨ (¬ p4539))
    : p2901 ∨ (¬ p3051) ∨ p2563 ∨ (¬ p2284) ∨ (¬ p4539) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4539 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41358 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step78127 (p2156 p2177 p2284 p2299 p2901 p3646 p4275 p4320 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73234 : p2299 ∨ p2177)
    (h73436 : p3646 ∨ p2156)
    (h51592 : (¬ p2284) ∨ (¬ p2299) ∨ (¬ p3646) ∨ (¬ p4275) ∨ (¬ p4320))
    : p2901 ∨ (¬ p2284) ∨ p2177 ∨ (¬ p4275) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51592 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78129 (p2156 p2284 p2737 p2743 p2901 p2950 p3361 p3646 p4320 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73298 : p2743 ∨ p2737)
    (h73436 : p3646 ∨ p2156)
    (h45283 : (¬ p2284) ∨ (¬ p2743) ∨ (¬ p2950) ∨ (¬ p3361) ∨ (¬ p3646) ∨ (¬ p4320))
    : (¬ p2284) ∨ p2901 ∨ (¬ p2950) ∨ p2737 ∨ (¬ p3361) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h45283 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step78130 (p2177 p2299 p2901 p3156 p4042 p4320 p4559 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73234 : p2299 ∨ p2177)
    (h52582 : (¬ p2299) ∨ (¬ p3156) ∨ (¬ p4042) ∨ (¬ p4320) ∨ (¬ p4559))
    : p2901 ∨ (¬ p3156) ∨ (¬ p4042) ∨ (¬ p4559) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h52582 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step78134 (p2166 p2191 p2901 p3156 p3246 p3368 p3690 p4320 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73446 : p3690 ∨ p3246)
    (h73222 : p2191 ∨ p2166)
    (h55895 : (¬ p2191) ∨ (¬ p3156) ∨ (¬ p3368) ∨ (¬ p3690) ∨ (¬ p4320))
    : p2901 ∨ (¬ p3156) ∨ (¬ p3368) ∨ p3246 ∨ p2166 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2191 := (Or.elim h73222 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55895 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78135 (p2284 p2901 p3125 p4275 p4320 p4624 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h60046 : (¬ p2284) ∨ (¬ p3125) ∨ (¬ p4275) ∨ (¬ p4320) ∨ (¬ p4624))
    : (¬ p3125) ∨ p2901 ∨ (¬ p4275) ∨ (¬ p4624) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4624 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h60046 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step78138 (p2252 p2608 p2750 p2901 p2946 p2952 p3246 p3399 p3527 p3690 p3954 p4320 p4666 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73446 : p3690 ∨ p3246)
    (h73330 : p2952 ∨ p2946)
    (h73552 : p4320 ∨ p2901)
    (h64844 : (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3690) ∨ (¬ p3954) ∨ (¬ p4320) ∨ (¬ p4666))
    : p2608 ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p4666) ∨ (¬ p3399) ∨ (¬ p3527) ∨ p3246 ∨ p2946 ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h64844 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step78139 (p2177 p2299 p2396 p2901 p3246 p3690 p4320 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73234 : p2299 ∨ p2177)
    (h73552 : p4320 ∨ p2901)
    (h43848 : (¬ p2299) ∨ (¬ p2396) ∨ (¬ p3690) ∨ (¬ p4320))
    : (¬ p2396) ∨ p3246 ∨ p2177 ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43848 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step78140 (p2156 p2284 p2881 p2901 p3570 p3646 p4320 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73418 : p3570 ∨ p2881)
    (h73436 : p3646 ∨ p2156)
    (h65241 : (¬ p2284) ∨ (¬ p3570) ∨ (¬ p3646) ∨ (¬ p4320))
    : p2901 ∨ (¬ p2284) ∨ p2881 ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h65241 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78143 (p2156 p2901 p3051 p3156 p3646 p4320 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73436 : p3646 ∨ p2156)
    (h46722 : (¬ p3051) ∨ (¬ p3156) ∨ (¬ p3646) ∨ (¬ p4320))
    : p2901 ∨ (¬ p3156) ∨ p2156 ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46722 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78144 (p2254 p2901 p2946 p2952 p3193 p3222 p3276 p3379 p4320 p4831 p5660 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73330 : p2952 ∨ p2946)
    (h73552 : p4320 ∨ p2901)
    (h51036 : (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3379) ∨ (¬ p4320) ∨ (¬ p4831) ∨ (¬ p5660))
    : p3193 ∨ (¬ p4831) ∨ p2946 ∨ p2901 ∨ (¬ p3379) ∨ (¬ p2254) ∨ (¬ p3276) ∨ (¬ p5660) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h51036 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step78147 (p2901 p2911 p3156 p3644 p4042 p4277 p4320 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73552 : p4320 ∨ p2901)
    (h41020 : (¬ p3156) ∨ (¬ p3644) ∨ (¬ p4042) ∨ (¬ p4277) ∨ (¬ p4320))
    : (¬ p4042) ∨ (¬ p3156) ∨ (¬ p4277) ∨ p2911 ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4042 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41020 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step78148 (p2254 p2417 p2881 p2901 p2922 p2946 p2952 p3379 p3570 p4320 p4668 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73418 : p3570 ∨ p2881)
    (h73552 : p4320 ∨ p2901)
    (h49491 : (¬ p2254) ∨ (¬ p2417) ∨ (¬ p2922) ∨ (¬ p2952) ∨ (¬ p3379) ∨ (¬ p3570) ∨ (¬ p4320) ∨ (¬ p4668))
    : p2946 ∨ (¬ p2254) ∨ (¬ p3379) ∨ p2881 ∨ (¬ p2922) ∨ (¬ p2417) ∨ p2901 ∨ (¬ p4668) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h49491 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step78152 (p2651 p2881 p2901 p2946 p2952 p3570 p4320 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73552 : p4320 ∨ p2901)
    (h73418 : p3570 ∨ p2881)
    (h60103 : (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3570) ∨ (¬ p4320))
    : p2946 ∨ p2901 ∨ p2881 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h60103 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step78155 (p2737 p2743 p2881 p2901 p2946 p2952 p3361 p3570 p4320 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73330 : p2952 ∨ p2946)
    (h73418 : p3570 ∨ p2881)
    (h73298 : p2743 ∨ p2737)
    (h63226 : (¬ p2743) ∨ (¬ p2952) ∨ (¬ p3361) ∨ (¬ p3570) ∨ (¬ p4320))
    : p2901 ∨ p2946 ∨ p2881 ∨ (¬ p3361) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63226 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78156 (p2139 p2363 p2470 p2476 p2528 p2534 p2901 p3051 p3156 p3905 p4320 p4433 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73268 : p2534 ∨ p2528)
    (h73250 : p2476 ∨ p2470)
    (h60029 : (¬ p2139) ∨ (¬ p2363) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3051) ∨ (¬ p3156) ∨ (¬ p3905) ∨ (¬ p4320) ∨ (¬ p4433))
    : p2901 ∨ (¬ p3156) ∨ p2528 ∨ (¬ p3905) ∨ p2470 ∨ (¬ p4433) ∨ (¬ p2139) ∨ (¬ p3051) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h60029 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step78158 (p2459 p2881 p2901 p2946 p2952 p3570 p4320 p4348 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73562 : p4348 ∨ p2459)
    (h73552 : p4320 ∨ p2901)
    (h73330 : p2952 ∨ p2946)
    (h42884 : (¬ p2952) ∨ (¬ p3570) ∨ (¬ p4320) ∨ (¬ p4348))
    : p2881 ∨ p2459 ∨ p2901 ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42884 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step78159 (p2881 p2901 p2946 p2952 p3570 p4320 p5558 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73418 : p3570 ∨ p2881)
    (h73552 : p4320 ∨ p2901)
    (h63098 : (¬ p2952) ∨ (¬ p3570) ∨ (¬ p4320) ∨ (¬ p5558))
    : (¬ p5558) ∨ p2946 ∨ p2881 ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5558 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63098 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step78167 (p2630 p2810 p2870 p2901 p2946 p2952 p4313 p4320 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73316 : p2810 ∨ p2630)
    (h73330 : p2952 ∨ p2946)
    (h50966 : (¬ p2810) ∨ (¬ p2870) ∨ (¬ p2952) ∨ (¬ p4313) ∨ (¬ p4320))
    : (¬ p4313) ∨ p2901 ∨ p2630 ∨ p2946 ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50966 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78171 (p2254 p2608 p2819 p2829 p2881 p2901 p2946 p2952 p3570 p4133 p4320 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73552 : p4320 ∨ p2901)
    (h73330 : p2952 ∨ p2946)
    (h57994 : (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p2952) ∨ (¬ p3570) ∨ (¬ p4133) ∨ (¬ p4320))
    : (¬ p2829) ∨ (¬ p2819) ∨ p2881 ∨ (¬ p2254) ∨ (¬ p4133) ∨ (¬ p2608) ∨ p2901 ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u10 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h57994 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u9)))))))))))))))))

theorem step78174 (p2187 p2284 p2901 p4275 p4320 p4405 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h41831 : (¬ p2187) ∨ (¬ p2284) ∨ (¬ p4275) ∨ (¬ p4320) ∨ (¬ p4405))
    : p2901 ∨ (¬ p2284) ∨ (¬ p2187) ∨ (¬ p4405) ∨ (¬ p4275) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41831 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step78178 (p2284 p2901 p3246 p3516 p3690 p4320 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73552 : p4320 ∨ p2901)
    (h45812 : (¬ p2284) ∨ (¬ p3516) ∨ (¬ p3690) ∨ (¬ p4320))
    : (¬ p3516) ∨ p3246 ∨ (¬ p2284) ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45812 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step78180 (p2341 p2881 p2901 p3570 p3575 p3741 p4320 p4702 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73418 : p3570 ∨ p2881)
    (h53543 : (¬ p2341) ∨ (¬ p3570) ∨ (¬ p3575) ∨ (¬ p3741) ∨ (¬ p4320) ∨ (¬ p4702))
    : (¬ p2341) ∨ p2901 ∨ (¬ p3575) ∨ p2881 ∨ (¬ p3741) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53543 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step78181 (p2254 p2774 p2829 p2881 p2901 p2946 p2952 p3537 p3570 p3589 p3688 p4320 p4802 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73552 : p4320 ∨ p2901)
    (h73330 : p2952 ∨ p2946)
    (h73418 : p3570 ∨ p2881)
    (h49056 : (¬ p2254) ∨ (¬ p2774) ∨ (¬ p2952) ∨ (¬ p3537) ∨ (¬ p3570) ∨ (¬ p3589) ∨ (¬ p3688) ∨ (¬ p4320) ∨ (¬ p4802))
    : p2829 ∨ (¬ p3537) ∨ (¬ p2254) ∨ (¬ p3589) ∨ p2901 ∨ p2946 ∨ (¬ p2774) ∨ p2881 ∨ (¬ p4802) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4802 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h49056 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step78183 (p2254 p2608 p2707 p2881 p2901 p2946 p2952 p3434 p3570 p4320 p4668 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73418 : p3570 ∨ p2881)
    (h73552 : p4320 ∨ p2901)
    (h50273 : (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2952) ∨ (¬ p3434) ∨ (¬ p3570) ∨ (¬ p4320) ∨ (¬ p4668))
    : (¬ p3434) ∨ p2946 ∨ (¬ p2707) ∨ p2881 ∨ (¬ p2608) ∨ (¬ p2254) ∨ (¬ p4668) ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h50273 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step78184 (p2352 p2363 p2573 p2579 p2744 p2901 p3051 p3115 p3347 p3370 p3956 p4257 p4320 p4347 p4365 p4450 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73274 : p2579 ∨ p2573)
    (h73500 : p3956 ∨ p2352)
    (h73552 : p4320 ∨ p2901)
    (h63873 : (¬ p2579) ∨ (¬ p2744) ∨ (¬ p3051) ∨ (¬ p3115) ∨ (¬ p3347) ∨ (¬ p3370) ∨ (¬ p3956) ∨ (¬ p4257) ∨ (¬ p4320) ∨ (¬ p4347) ∨ (¬ p4365) ∨ (¬ p4450))
    : (¬ p3370) ∨ p2363 ∨ p2573 ∨ (¬ p3051) ∨ (¬ p3347) ∨ (¬ p2744) ∨ (¬ p4257) ∨ (¬ p3115) ∨ p2352 ∨ p2901 ∨ (¬ p4365) ∨ (¬ p4450) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3370 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u13 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u14 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u15 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h63873 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u14))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u15))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u10))) (fun r10 => (False.elim (r10 u11)))))))))))))))))))))))))

theorem step78185 (p2427 p2651 p2901 p2946 p2952 p4320 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73552 : p4320 ∨ p2901)
    (h45782 : (¬ p2427) ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p4320))
    : p2946 ∨ p2901 ∨ (¬ p2651) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45782 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step78187 (p2248 p2509 p2528 p2534 p2901 p2958 p3051 p3115 p3379 p3452 p3950 p4135 p4320 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73394 : p3452 ∨ p3379)
    (h73268 : p2534 ∨ p2528)
    (h48881 : (¬ p2248) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p3115) ∨ (¬ p3452) ∨ (¬ p3950) ∨ (¬ p4135) ∨ (¬ p4320))
    : (¬ p3115) ∨ p2901 ∨ (¬ p2248) ∨ (¬ p2958) ∨ p3379 ∨ p2528 ∨ (¬ p4135) ∨ (¬ p2509) ∨ (¬ p3950) ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4135 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h48881 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u10)))))))))))))))))))))

theorem step78188 (p2132 p2138 p2284 p2860 p2901 p3758 p4320 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73456 : p3758 ∨ p2860)
    (h73214 : p2138 ∨ p2132)
    (h42910 : (¬ p2138) ∨ (¬ p2284) ∨ (¬ p3758) ∨ (¬ p4320))
    : (¬ p2284) ∨ p2901 ∨ p2860 ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42910 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78189 (p2139 p2352 p2598 p2901 p3051 p3055 p3156 p3422 p3584 p3956 p4320 p4433 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73426 : p3584 ∨ p3422)
    (h73350 : p3055 ∨ p2598)
    (h73500 : p3956 ∨ p2352)
    (h49152 : (¬ p2139) ∨ (¬ p3051) ∨ (¬ p3055) ∨ (¬ p3156) ∨ (¬ p3584) ∨ (¬ p3956) ∨ (¬ p4320) ∨ (¬ p4433))
    : p2901 ∨ (¬ p3156) ∨ p3422 ∨ (¬ p2139) ∨ p2598 ∨ p2352 ∨ (¬ p3051) ∨ (¬ p4433) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h49152 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step78197 (p2901 p2946 p2952 p3166 p4311 p4320 p4904 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73330 : p2952 ∨ p2946)
    (h41922 : (¬ p2952) ∨ (¬ p3166) ∨ (¬ p4311) ∨ (¬ p4320) ∨ (¬ p4904))
    : (¬ p4311) ∨ (¬ p3166) ∨ (¬ p4904) ∨ p2901 ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4311 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41922 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step78198 (p2230 p2440 p2901 p3051 p4320 p4537 p4699 : Prop)
    (h73624 : p4537 ∨ (¬ p2230))
    (h73552 : p4320 ∨ p2901)
    (h73712 : p4699 ∨ (¬ p2440))
    (h66962 : (¬ p4537) ∨ (¬ p4699) ∨ (¬ p4320) ∨ (¬ p3051))
    : (¬ p2230) ∨ (¬ p3051) ∨ p2901 ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4537 := (Or.elim h73624 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u5 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4699 := (Or.elim h73712 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h66962 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step78199 (p2156 p2563 p2901 p3051 p3646 p4320 p4702 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73436 : p3646 ∨ p2156)
    (h48083 : (¬ p2563) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4320) ∨ (¬ p4702))
    : p2901 ∨ (¬ p3051) ∨ (¬ p2563) ∨ (¬ p4702) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48083 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step78202 (p2651 p2657 p2901 p2958 p3051 p4320 p4704 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73288 : p2657 ∨ p2651)
    (h73046 : p4704)
    (h52046 : (¬ p2657) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p4320) ∨ (¬ p4704))
    : p2901 ∨ p2651 ∨ (¬ p3051) ∨ (¬ p2958) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4704 := h73046;
    (Or.elim h52046 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step78208 (p2901 p3146 p3256 p3692 p3988 p4237 p4320 p4555 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73552 : p4320 ∨ p2901)
    (h41499 : (¬ p3256) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4237) ∨ (¬ p4320) ∨ (¬ p4555))
    : (¬ p3256) ∨ p3146 ∨ p2901 ∨ (¬ p3988) ∨ (¬ p4237) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4237 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41499 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step78209 (p2901 p3146 p3256 p3692 p4237 p4320 p4904 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73552 : p4320 ∨ p2901)
    (h55554 : (¬ p3256) ∨ (¬ p3692) ∨ (¬ p4237) ∨ (¬ p4320) ∨ (¬ p4904))
    : (¬ p3256) ∨ p3146 ∨ (¬ p4237) ∨ (¬ p4904) ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4237 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55554 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step78210 (p2295 p2901 p3568 p4275 p4320 p4336 : Prop)
    (h73415 : (¬ p2295) ∨ (¬ p3568))
    (h73552 : p4320 ∨ p2901)
    (h38552 : p3568 ∨ (¬ p4275) ∨ (¬ p4320) ∨ (¬ p4336))
    : (¬ p2295) ∨ (¬ p4275) ∨ p2901 ∨ (¬ p4336) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3568) := (Or.elim h73415 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u5 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h38552 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step78213 (p2901 p4916 p4917 : Prop)
    (h73826 : p4916 ∨ p2901)
    (h8122 : (¬ p4916) ∨ p4917)
    : p2901 ∨ p4917 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4917) := (fun h => hn (Or.inr h));
    let u2 : p4916 := (Or.elim h73826 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h8122 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step78214 (p2901 p4280 p4916 : Prop)
    (h73826 : p4916 ∨ p2901)
    (h8123 : p4280 ∨ (¬ p4916))
    : p4280 ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4280) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr h));
    let u2 : p4916 := (Or.elim h73826 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h8123 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step78220 (p2651 p2661 p2662 : Prop)
    (h73292 : p2661 ∨ (¬ p2651))
    (h3447 : (¬ p2661) ∨ p2662)
    : (¬ p2651) ∨ p2662 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2662) := (fun h => hn (Or.inr h));
    let u2 : p2661 := (Or.elim h73292 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h3447 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step78221 (p2651 p2661 p2663 : Prop)
    (h73292 : p2661 ∨ (¬ p2651))
    (h3448 : (¬ p2661) ∨ p2663)
    : (¬ p2651) ∨ p2663 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2663) := (fun h => hn (Or.inr h));
    let u2 : p2661 := (Or.elim h73292 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h3448 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step78222 (p2651 p2661 p2664 : Prop)
    (h73292 : p2661 ∨ (¬ p2651))
    (h3450 : (¬ p2661) ∨ p2664)
    : (¬ p2651) ∨ p2664 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2664) := (fun h => hn (Or.inr h));
    let u2 : p2661 := (Or.elim h73292 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h3450 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step78223 (p2651 p2661 p2665 : Prop)
    (h73292 : p2661 ∨ (¬ p2651))
    (h3451 : (¬ p2661) ∨ p2665)
    : (¬ p2651) ∨ p2665 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2665) := (fun h => hn (Or.inr h));
    let u2 : p2661 := (Or.elim h73292 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h3451 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step78224 (p2427 p2440 p2542 p2651 p2737 p2811 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h44904 : (¬ p2427) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2737) ∨ (¬ p2811))
    : (¬ p2811) ∨ (¬ p2737) ∨ (¬ p2427) ∨ (¬ p2651) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2811 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h44904 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step78225 (p2363 p2510 p2528 p2651 p3016 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h43740 : (¬ p2510) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p4347))
    : p2363 ∨ (¬ p2528) ∨ (¬ p3016) ∨ (¬ p2651) ∨ (¬ p2510) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2510 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h43740 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78226 (p2373 p2440 p2542 p2651 p3146 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h45174 : (¬ p2373) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p3146))
    : (¬ p2651) ∨ (¬ p3146) ∨ (¬ p2373) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45174 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step78228 (p2437 p2459 p2528 p2651 p3875 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h43559 : (¬ p2437) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3875) ∨ (¬ p4348))
    : (¬ p2437) ∨ p2459 ∨ (¬ p2528) ∨ (¬ p3875) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43559 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78229 (p2220 p2651 p3156 p3497 p4120 : Prop)
    (h73399 : (¬ p3156) ∨ (¬ p3497))
    (h73522 : p4120 ∨ p2220)
    (h69610 : p3497 ∨ (¬ p4120) ∨ (¬ p2651))
    : (¬ p3156) ∨ p2220 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3497) := (Or.elim h73399 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h69610 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u2)))))))

theorem step78230 (p2528 p2651 p3083 p3146 p3692 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h43379 : (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p3692))
    : (¬ p3083) ∨ (¬ p2528) ∨ p3146 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3083 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43379 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78231 (p2295 p2331 p2651 p2727 p2963 p3568 p4111 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73518 : p4111 ∨ p2727)
    (h73416 : p3568 ∨ p2295)
    (h43604 : (¬ p2651) ∨ (¬ p2963) ∨ (¬ p3568) ∨ (¬ p4111))
    : (¬ p2651) ∨ p2331 ∨ p2727 ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43604 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step78232 (p2156 p2295 p2651 p3156 p3497 p3568 p3646 p4153 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73399 : (¬ p3156) ∨ (¬ p3497))
    (h73436 : p3646 ∨ p2156)
    (h69611 : (¬ p3646) ∨ (¬ p4153) ∨ (¬ p2651) ∨ p3497 ∨ (¬ p3568))
    : p2295 ∨ (¬ p4153) ∨ (¬ p2651) ∨ (¬ p3156) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2295) := (fun h => hn (Or.inl h));
    let u1 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : (¬ p3497) := (Or.elim h73399 (fun q0 => (False.elim (q0 u3))) (fun r0 => r0));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h69611 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78233 (p2440 p2651 p2807 p2901 p3414 p4703 : Prop)
    (h73392 : p3414 ∨ p2807)
    (h73714 : p4703 ∨ p2440)
    (h66891 : (¬ p4703) ∨ p2901 ∨ (¬ p3414) ∨ (¬ p2651))
    : p2901 ∨ (¬ p2651) ∨ p2807 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4703 := (Or.elim h73714 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h66891 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step78235 (p2553 p2651 p3016 p3286 p3292 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h43748 : (¬ p2553) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3292))
    : p3286 ∨ (¬ p2553) ∨ (¬ p3016) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3286) := (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h43748 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78236 (p2248 p2363 p2440 p2542 p2651 p2982 p3093 p3591 p3923 p4347 p4450 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73432 : p3591 ∨ p3093)
    (h73270 : p2542 ∨ p2440)
    (h48854 : (¬ p2248) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2982) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4347) ∨ (¬ p4450))
    : (¬ p2982) ∨ p2363 ∨ p3093 ∨ (¬ p4450) ∨ (¬ p3923) ∨ (¬ p2651) ∨ p2440 ∨ (¬ p2248) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h48854 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step78238 (p2440 p2542 p2651 p2982 p3680 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h45080 : (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2982) ∨ (¬ p3680))
    : (¬ p2651) ∨ (¬ p2982) ∨ p2440 ∨ (¬ p3680) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45080 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step78240 (p2373 p2440 p2542 p2651 p3969 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h61658 : (¬ p2373) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p3969))
    : (¬ p3969) ∨ p2440 ∨ (¬ p2373) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h61658 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step78241 (p2156 p2284 p2651 p2950 p3646 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h69612 : (¬ p3646) ∨ (¬ p2950) ∨ (¬ p2284) ∨ (¬ p2651))
    : (¬ p2284) ∨ (¬ p2950) ∨ p2156 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h69612 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step78242 (p2427 p2440 p2542 p2651 p2881 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h45540 : (¬ p2427) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2881))
    : (¬ p2427) ∨ (¬ p2881) ∨ p2440 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45540 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step78243 (p2295 p2307 p2313 p2651 p3983 p4972 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h51734 : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2651) ∨ (¬ p3983) ∨ (¬ p4972))
    : (¬ p3983) ∨ p2307 ∨ (¬ p2295) ∨ (¬ p4972) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3983 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h51734 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step78245 (p2946 p2956 p2957 : Prop)
    (h73334 : p2956 ∨ (¬ p2946))
    (h4040 : (¬ p2956) ∨ p2957)
    : (¬ p2946) ∨ p2957 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2957) := (fun h => hn (Or.inr h));
    let u2 : p2956 := (Or.elim h73334 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h4040 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step78248 (p2946 p2956 p2960 : Prop)
    (h73334 : p2956 ∨ (¬ p2946))
    (h4044 : (¬ p2956) ∨ p2960)
    : (¬ p2946) ∨ p2960 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2960) := (fun h => hn (Or.inr h));
    let u2 : p2956 := (Or.elim h73334 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h4044 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step78249 (p2230 p4031 p4537 : Prop)
    (h73624 : p4537 ∨ (¬ p2230))
    (h7146 : p4031 ∨ (¬ p4537))
    : p4031 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4031) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4537 := (Or.elim h73624 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h7146 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step78252 (p2230 p4537 p4539 : Prop)
    (h73624 : p4537 ∨ (¬ p2230))
    (h7150 : (¬ p4537) ∨ p4539)
    : (¬ p2230) ∨ p4539 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4539) := (fun h => hn (Or.inr h));
    let u2 : p4537 := (Or.elim h73624 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h7150 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step78255 (p2427 p4643 p4644 : Prop)
    (h73684 : p4643 ∨ p2427)
    (h7430 : (¬ p4643) ∨ p4644)
    : p2427 ∨ p4644 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2427) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4644) := (fun h => hn (Or.inr h));
    let u2 : p4643 := (Or.elim h73684 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7430 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step78256 (p2427 p4277 p4643 : Prop)
    (h73684 : p4643 ∨ p2427)
    (h7431 : p4277 ∨ (¬ p4643))
    : p4277 ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4277) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr h));
    let u2 : p4643 := (Or.elim h73684 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h7431 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step78257 (p2156 p2284 p2651 p2657 p2958 p3952 p4704 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73046 : p4704)
    (h73288 : p2657 ∨ p2651)
    (h48790 : (¬ p2156) ∨ (¬ p2657) ∨ (¬ p2958) ∨ (¬ p3952) ∨ (¬ p4704))
    : (¬ p2958) ∨ p2284 ∨ (¬ p2156) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2958 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4704 := h73046;
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48790 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78258 (p2274 p2307 p2563 p2962 p3097 p4110 p4539 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73516 : p4110 ∨ p2563)
    (h54560 : (¬ p2307) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4539))
    : (¬ p2307) ∨ p2274 ∨ (¬ p2962) ∨ p2563 ∨ (¬ p4539) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4539 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54560 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step78259 (p2417 p2441 p3051 p3246 p4278 p4539 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h55801 : (¬ p2441) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p4278) ∨ (¬ p4539))
    : p2417 ∨ (¬ p3246) ∨ (¬ p2441) ∨ (¬ p3051) ∨ (¬ p4539) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4539 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h55801 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step78261 (p2156 p2590 p3125 p3564 p4137 p4539 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h49330 : (¬ p2156) ∨ (¬ p2590) ∨ (¬ p3125) ∨ (¬ p4137) ∨ (¬ p4539))
    : (¬ p3125) ∨ p3564 ∨ (¬ p2590) ∨ (¬ p4539) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4539 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h49330 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step78264 (p2230 p2563 p3389 p3540 p4001 p4555 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h53217 : (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3540) ∨ (¬ p4001) ∨ (¬ p4555))
    : p3389 ∨ (¬ p4001) ∨ (¬ p2563) ∨ (¬ p4555) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3389) := (fun h => hn (Or.inl h));
    let u1 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h53217 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step78268 (p2230 p2891 p3389 p3540 p4001 p4632 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h62315 : (¬ p2230) ∨ (¬ p2891) ∨ (¬ p3540) ∨ (¬ p4001) ∨ (¬ p4632))
    : (¬ p2891) ∨ (¬ p2230) ∨ p3389 ∨ (¬ p4632) ∨ (¬ p4001) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h62315 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step78270 (p2187 p3868 p3872 p3989 p4001 p4260 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h71390 : (¬ p4260) ∨ (¬ p3868) ∨ (¬ p3872) ∨ (¬ p3989) ∨ (¬ p4001))
    : (¬ p3868) ∨ (¬ p4260) ∨ (¬ p4001) ∨ (¬ p3872) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3868 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h71390 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step78272 (p2177 p2274 p2331 p2946 p2952 p3986 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h47779 : (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3986))
    : (¬ p2331) ∨ p2946 ∨ (¬ p2177) ∨ (¬ p3986) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47779 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step78274 (p2187 p2274 p2383 p2946 p2952 p3987 p3989 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h73330 : p2952 ∨ p2946)
    (h43656 : (¬ p2274) ∨ (¬ p2383) ∨ (¬ p2952) ∨ (¬ p3987) ∨ (¬ p3989))
    : (¬ p2383) ∨ (¬ p2274) ∨ (¬ p3987) ∨ p2187 ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43656 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78276 (p2139 p2156 p2274 p2396 p2528 p2534 p2651 p2657 p3083 p3950 p4236 p4256 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73542 : p4256 ∨ p3083)
    (h73288 : p2657 ∨ p2651)
    (h42408 : (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p3950) ∨ (¬ p4236) ∨ (¬ p4256))
    : p2528 ∨ (¬ p2396) ∨ (¬ p4236) ∨ p3083 ∨ (¬ p2274) ∨ p2651 ∨ (¬ p2139) ∨ (¬ p3950) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h42408 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u10)))))))))))))))))))

theorem step78280 (p2307 p2313 p2383 p2387 p3325 : Prop)
    (h73237 : (¬ p2307) ∨ (¬ p2313))
    (h73246 : p2387 ∨ p2383)
    (h6807 : p2313 ∨ (¬ p2387) ∨ (¬ p3325))
    : (¬ p3325) ∨ (¬ p2307) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3325 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2313) := (Or.elim h73237 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u4 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h6807 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u0)))))))

theorem step78284 (p2177 p2307 p2881 p3246 p3570 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h47672 : (¬ p2177) ∨ (¬ p2307) ∨ (¬ p3246) ∨ (¬ p3570))
    : (¬ p3246) ∨ p2881 ∨ (¬ p2307) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47672 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78285 (p2307 p3654 p3946 p4187 : Prop)
    (h73492 : p3946 ∨ p3654)
    (h9918 : (¬ p2307) ∨ (¬ p3946) ∨ (¬ p4187))
    : (¬ p4187) ∨ p3654 ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3654) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h9918 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u0)))))))

theorem step78289 (p2177 p2307 p3125 p3654 p3946 : Prop)
    (h73492 : p3946 ∨ p3654)
    (h55886 : (¬ p2177) ∨ (¬ p2307) ∨ (¬ p3125) ∨ (¬ p3946))
    : (¬ p2307) ∨ p3654 ∨ (¬ p3125) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3654) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h55886 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78293 (p2307 p2383 p2387 p2553 p2588 p3016 p3574 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73246 : p2387 ∨ p2383)
    (h73282 : p2588 ∨ p2553)
    (h43303 : (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2588) ∨ (¬ p3574))
    : (¬ p2307) ∨ p3016 ∨ p2383 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43303 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78298 (p2177 p2307 p2586 p2911 p3581 p3644 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h40992 : (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2586) ∨ (¬ p3581) ∨ (¬ p3644))
    : p2911 ∨ (¬ p2307) ∨ (¬ p2177) ∨ (¬ p2586) ∨ (¬ p3581) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2586 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h40992 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78300 (p2177 p2307 p2881 p3570 p4204 p4489 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h50477 : (¬ p2177) ∨ (¬ p2307) ∨ (¬ p3570) ∨ (¬ p4204) ∨ (¬ p4489))
    : (¬ p2307) ∨ (¬ p4204) ∨ p2881 ∨ (¬ p4489) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4489 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50477 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step78302 (p2307 p2396 p2578 p3564 p4137 p4625 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h41391 : (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2578) ∨ (¬ p4137) ∨ (¬ p4625))
    : (¬ p2396) ∨ (¬ p2307) ∨ (¬ p2578) ∨ p3564 ∨ (¬ p4625) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41391 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step78308 (p2307 p2383 p2387 p2553 p2588 p2819 p5225 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h73282 : p2588 ∨ p2553)
    (h48202 : (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2588) ∨ (¬ p2819) ∨ (¬ p5225))
    : (¬ p2307) ∨ (¬ p2819) ∨ p2383 ∨ p2553 ∨ (¬ p5225) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5225 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48202 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step78310 (p2274 p2307 p3097 p3743 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h19942 : (¬ p2307) ∨ (¬ p3097) ∨ (¬ p3743))
    : (¬ p2307) ∨ (¬ p3743) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h19942 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step78312 (p2295 p2307 p2641 p3568 p3654 p3946 p4154 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73526 : p4154 ∨ p2641)
    (h73492 : p3946 ∨ p3654)
    (h44327 : (¬ p2307) ∨ (¬ p3568) ∨ (¬ p3946) ∨ (¬ p4154))
    : p2295 ∨ p2641 ∨ (¬ p2307) ∨ p3654 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2295) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44327 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step78313 (p2295 p2307 p2946 p2952 p3568 p3987 p4566 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73416 : p3568 ∨ p2295)
    (h46986 : (¬ p2307) ∨ (¬ p2952) ∨ (¬ p3568) ∨ (¬ p3987) ∨ (¬ p4566))
    : (¬ p3987) ∨ p2946 ∨ (¬ p2307) ∨ p2295 ∨ (¬ p4566) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3987 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4566 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46986 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step78317 (p2274 p2284 p2307 p2960 p2962 p3097 p3952 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73352 : p3097 ∨ p2274)
    (h49444 : (¬ p2307) ∨ (¬ p2960) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p3952))
    : (¬ p2307) ∨ p2284 ∨ p2274 ∨ (¬ p2960) ∨ (¬ p2962) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h49444 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78318 (p2187 p2274 p2307 p2951 p2962 p2992 p3097 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h44821 : (¬ p2187) ∨ (¬ p2307) ∨ (¬ p2951) ∨ (¬ p2962) ∨ (¬ p2992) ∨ (¬ p3097))
    : (¬ p2187) ∨ p2274 ∨ (¬ p2307) ∨ (¬ p2951) ∨ (¬ p2962) ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h44821 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step78320 (p2187 p2274 p2307 p2850 p2962 p3097 p4109 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h62461 : (¬ p2187) ∨ (¬ p2307) ∨ (¬ p2850) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p4109))
    : (¬ p4109) ∨ p2274 ∨ (¬ p2307) ∨ (¬ p2850) ∨ (¬ p2962) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4109 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h62461 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step78321 (p2122 p2307 p2383 p2387 p2829 p3688 p3822 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73444 : p3688 ∨ p2829)
    (h73246 : p2387 ∨ p2383)
    (h44354 : (¬ p2307) ∨ (¬ p2387) ∨ (¬ p3688) ∨ (¬ p3822))
    : p2122 ∨ p2829 ∨ p2383 ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44354 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78329 (p2132 p2138 p2177 p2307 p2786 p2881 p3570 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73418 : p3570 ∨ p2881)
    (h54710 : (¬ p2138) ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2786) ∨ (¬ p3570))
    : (¬ p2307) ∨ (¬ p2786) ∨ p2132 ∨ p2881 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54710 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step78332 (p2307 p2417 p3654 p3946 p4396 p4712 : Prop)
    (h73492 : p3946 ∨ p3654)
    (h62359 : (¬ p2307) ∨ (¬ p2417) ∨ (¬ p3946) ∨ (¬ p4396) ∨ (¬ p4712))
    : (¬ p2417) ∨ p3654 ∨ (¬ p2307) ∨ (¬ p4712) ∨ (¬ p4396) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3654) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h62359 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step78342 (p2307 p2363 p2459 p2608 p3325 p3367 p3585 p3641 p3874 p3954 p4348 p4438 p5017 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h73562 : p4348 ∨ p2459)
    (h73484 : p3874 ∨ p3641)
    (h73498 : p3954 ∨ p2608)
    (h42572 : (¬ p2307) ∨ (¬ p2363) ∨ (¬ p3325) ∨ (¬ p3585) ∨ (¬ p3874) ∨ (¬ p3954) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p5017))
    : (¬ p2307) ∨ (¬ p5017) ∨ p3367 ∨ p2459 ∨ (¬ p3325) ∨ (¬ p2363) ∨ p3641 ∨ (¬ p4438) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5017 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h42572 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step78349 (p2187 p2307 p3325 p3743 p3989 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h24933 : (¬ p2307) ∨ (¬ p3325) ∨ (¬ p3743) ∨ (¬ p3989))
    : (¬ p3325) ∨ (¬ p2307) ∨ (¬ p3743) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3325 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h24933 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78351 (p2307 p2383 p2387 p2911 p4138 p4712 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h50408 : (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2911) ∨ (¬ p4138) ∨ (¬ p4712))
    : (¬ p2911) ∨ (¬ p2307) ∨ (¬ p4712) ∨ (¬ p4138) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50408 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step78352 (p2307 p2383 p2387 p2881 p4138 p4559 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h41877 : (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2881) ∨ (¬ p4138) ∨ (¬ p4559))
    : (¬ p2881) ∨ (¬ p2307) ∨ (¬ p4559) ∨ p2383 ∨ (¬ p4138) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41877 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step78353 (p2307 p2383 p2387 p2459 p2553 p2588 p4138 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73246 : p2387 ∨ p2383)
    (h73282 : p2588 ∨ p2553)
    (h48398 : (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2588) ∨ (¬ p4138) ∨ (¬ p4348))
    : p2459 ∨ (¬ p2307) ∨ p2383 ∨ (¬ p4138) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48398 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78358 (p2274 p2307 p2363 p2383 p2387 p3097 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73246 : p2387 ∨ p2383)
    (h73352 : p3097 ∨ p2274)
    (h45200 : (¬ p2307) ∨ (¬ p2387) ∨ (¬ p3097) ∨ (¬ p4347))
    : (¬ p2307) ∨ p2363 ∨ p2383 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45200 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78360 (p2307 p2363 p2383 p2387 p2553 p2588 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73282 : p2588 ∨ p2553)
    (h73246 : p2387 ∨ p2383)
    (h56014 : (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2588) ∨ (¬ p4347))
    : (¬ p2307) ∨ p2363 ∨ p2553 ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56014 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78361 (p2187 p2307 p2383 p2387 p2563 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h46890 : (¬ p2187) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2563))
    : (¬ p2307) ∨ (¬ p2187) ∨ p2383 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46890 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step78363 (p2264 p2307 p2383 p2387 p4138 p4361 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h58396 : (¬ p2264) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p4138) ∨ (¬ p4361))
    : (¬ p2264) ∨ (¬ p2307) ∨ (¬ p4361) ∨ (¬ p4138) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h58396 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step78364 (p2307 p2383 p2387 p2774 p2819 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h44382 : (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2774) ∨ (¬ p2819))
    : (¬ p2307) ∨ (¬ p2819) ∨ (¬ p2774) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44382 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step78366 (p2295 p2307 p2946 p2952 p3568 p3987 p4194 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73416 : p3568 ∨ p2295)
    (h69613 : (¬ p2307) ∨ (¬ p2952) ∨ (¬ p3987) ∨ (¬ p3568) ∨ (¬ p4194))
    : (¬ p3987) ∨ p2946 ∨ (¬ p2307) ∨ p2295 ∨ (¬ p4194) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3987 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69613 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step78370 (p2122 p2307 p2528 p2534 p2651 p2657 p2786 p3083 p3483 p3822 p4256 p4330 p4789 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73472 : p3822 ∨ p2122)
    (h73542 : p4256 ∨ p3083)
    (h73288 : p2657 ∨ p2651)
    (h53367 : (¬ p2307) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2786) ∨ (¬ p3483) ∨ (¬ p3822) ∨ (¬ p4256) ∨ (¬ p4330) ∨ (¬ p4789))
    : (¬ p3483) ∨ p2528 ∨ (¬ p4330) ∨ (¬ p2307) ∨ p2122 ∨ p3083 ∨ (¬ p2786) ∨ p2651 ∨ (¬ p4789) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h53367 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step78371 (p2139 p2274 p2307 p2528 p2534 p2651 p2657 p2962 p3083 p3097 p3125 p4236 p4256 p4330 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73542 : p4256 ∨ p3083)
    (h73288 : p2657 ∨ p2651)
    (h73352 : p3097 ∨ p2274)
    (h64525 : (¬ p2139) ∨ (¬ p2307) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p4236) ∨ (¬ p4256) ∨ (¬ p4330))
    : p2528 ∨ (¬ p3125) ∨ (¬ p2139) ∨ (¬ p4236) ∨ p3083 ∨ (¬ p4330) ∨ (¬ p2307) ∨ (¬ p2962) ∨ p2651 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u13 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h64525 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step78372 (p2307 p2363 p2383 p2387 p3309 p3549 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73406 : p3549 ∨ p3309)
    (h73246 : p2387 ∨ p2383)
    (h48441 : (¬ p2307) ∨ (¬ p2387) ∨ (¬ p3549) ∨ (¬ p4347))
    : (¬ p2307) ∨ p2363 ∨ p3309 ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48441 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78374 (p2307 p2363 p2406 p2459 p2962 p3325 p4109 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h55854 : (¬ p2307) ∨ (¬ p2363) ∨ (¬ p2406) ∨ (¬ p2962) ∨ (¬ p3325) ∨ (¬ p4109) ∨ (¬ p4348))
    : (¬ p2406) ∨ (¬ p2307) ∨ (¬ p4109) ∨ p2459 ∨ (¬ p3325) ∨ (¬ p2363) ∨ (¬ p2962) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55854 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u7)))))))))))))))

theorem step78377 (p2274 p2307 p3097 p3461 p3654 p3946 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73492 : p3946 ∨ p3654)
    (h73352 : p3097 ∨ p2274)
    (h58585 : (¬ p2307) ∨ (¬ p3097) ∨ (¬ p3946) ∨ (¬ p4191))
    : p3461 ∨ p3654 ∨ (¬ p2307) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3654) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h58585 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78378 (p2307 p3309 p3461 p3549 p3654 p3946 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73406 : p3549 ∨ p3309)
    (h73492 : p3946 ∨ p3654)
    (h43341 : (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3946) ∨ (¬ p4191))
    : p3461 ∨ (¬ p2307) ∨ p3309 ∨ p3654 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43341 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78380 (p2307 p2553 p2588 p3461 p3654 p3946 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73492 : p3946 ∨ p3654)
    (h73282 : p2588 ∨ p2553)
    (h57039 : (¬ p2307) ∨ (¬ p2588) ∨ (¬ p3946) ∨ (¬ p4191))
    : p3461 ∨ (¬ p2307) ∨ p3654 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h57039 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78387 (p2274 p2307 p2352 p2383 p2387 p3097 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h73352 : p3097 ∨ p2274)
    (h44508 : (¬ p2307) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p3097))
    : (¬ p2307) ∨ (¬ p2352) ∨ p2383 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44508 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step78392 (p2187 p2274 p2307 p3097 p3136 p3567 p4336 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h61184 : (¬ p2187) ∨ (¬ p2307) ∨ (¬ p3097) ∨ (¬ p3136) ∨ (¬ p3567) ∨ (¬ p4336))
    : p2274 ∨ (¬ p2187) ∨ (¬ p2307) ∨ (¬ p3567) ∨ (¬ p4336) ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h61184 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step78393 (p2187 p2307 p2962 p3063 p3309 p3549 p3989 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h73406 : p3549 ∨ p3309)
    (h43161 : (¬ p2307) ∨ (¬ p2962) ∨ (¬ p3063) ∨ (¬ p3549) ∨ (¬ p3989))
    : (¬ p3063) ∨ (¬ p2307) ∨ p2187 ∨ (¬ p2962) ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43161 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78394 (p2307 p2459 p2598 p2850 p2982 p3055 p3527 p3684 p4427 p4736 p4948 p5020 p5059 : Prop)
    (h73350 : p3055 ∨ p2598)
    (h73442 : p3684 ∨ p2850)
    (h73846 : p4948 ∨ p2982)
    (h49596 : (¬ p2307) ∨ (¬ p2459) ∨ (¬ p3055) ∨ (¬ p3527) ∨ (¬ p3684) ∨ (¬ p4427) ∨ (¬ p4736) ∨ (¬ p4948) ∨ (¬ p5020) ∨ (¬ p5059))
    : (¬ p3527) ∨ (¬ p2307) ∨ (¬ p5059) ∨ (¬ p2459) ∨ p2598 ∨ p2850 ∨ p2982 ∨ (¬ p4427) ∨ (¬ p4736) ∨ (¬ p5020) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h49596 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step78395 (p2307 p2396 p2417 p2586 p3581 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h41028 : (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2586) ∨ (¬ p3581) ∨ (¬ p4278))
    : (¬ p2396) ∨ p2417 ∨ (¬ p2307) ∨ (¬ p2586) ∨ (¬ p3581) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2586 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41028 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78396 (p2274 p2307 p2696 p2962 p3005 p3097 p3125 p3256 p3365 p3366 p3370 p3877 p3950 p4118 p4377 p4623 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h73352 : p3097 ∨ p2274)
    (h73390 : p3365 ∨ p2696)
    (h73488 : p3877 ∨ p3005)
    (h41983 : (¬ p2307) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4377) ∨ (¬ p4623))
    : p3256 ∨ (¬ p3370) ∨ p2274 ∨ (¬ p4623) ∨ (¬ p4377) ∨ (¬ p3366) ∨ (¬ p2307) ∨ p2696 ∨ p3005 ∨ (¬ p3125) ∨ (¬ p3950) ∨ (¬ p2962) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4623 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u13 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u14 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u15 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h41983 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u13))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u14))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u15))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u4))) (fun r10 => (False.elim (r10 u3)))))))))))))))))))))))))

theorem step78398 (p2122 p2187 p2307 p2383 p2387 p3822 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73246 : p2387 ∨ p2383)
    (h53380 : (¬ p2187) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p3822))
    : p2122 ∨ (¬ p2307) ∨ p2383 ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h53380 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78401 (p2307 p2383 p2387 p2459 p3146 p3692 p4441 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h73448 : p3692 ∨ p3146)
    (h53922 : (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2459) ∨ (¬ p3692) ∨ (¬ p4441))
    : (¬ p2307) ∨ (¬ p4441) ∨ p2383 ∨ (¬ p2459) ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h53922 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step78403 (p2190 p2274 p2307 p2363 p3097 p3146 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73352 : p3097 ∨ p2274)
    (h60988 : (¬ p2190) ∨ (¬ p2307) ∨ (¬ p3097) ∨ (¬ p3146) ∨ (¬ p4347))
    : p2363 ∨ (¬ p3146) ∨ (¬ p2307) ∨ p2274 ∨ (¬ p2190) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60988 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78404 (p2187 p2274 p2307 p2459 p3097 p3550 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h44696 : (¬ p2187) ∨ (¬ p2307) ∨ (¬ p2459) ∨ (¬ p3097) ∨ (¬ p3550))
    : p2274 ∨ (¬ p2307) ∨ (¬ p2459) ∨ (¬ p3550) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h44696 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step78405 (p2177 p2307 p2383 p2387 p2668 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h46610 : (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2668))
    : (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2668) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46610 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step78406 (p2274 p2307 p2383 p2387 p2668 p3097 p4560 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h72955 : p4560)
    (h73246 : p2387 ∨ p2383)
    (h53530 : (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2668) ∨ (¬ p3097) ∨ (¬ p4560))
    : (¬ p2668) ∨ (¬ p2307) ∨ p2274 ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4560 := h72955;
    let u6 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53530 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78409 (p2274 p2307 p2761 p3097 p3125 p4623 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h55765 : (¬ p2307) ∨ (¬ p2761) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p4623))
    : (¬ p2761) ∨ (¬ p2307) ∨ p2274 ∨ (¬ p4623) ∨ (¬ p3125) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4623 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h55765 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step78414 (p2352 p2383 p2387 p2578 p3956 : Prop)
    (h73245 : (¬ p2383) ∨ (¬ p2387))
    (h73500 : p3956 ∨ p2352)
    (h6827 : p2387 ∨ (¬ p2578) ∨ (¬ p3956))
    : (¬ p2578) ∨ (¬ p2383) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2578 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2387) := (Or.elim h73245 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u4 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h6827 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u4)))))))

theorem step78416 (p2383 p4113 p4615 : Prop)
    (h73670 : p4615 ∨ (¬ p2383))
    (h7365 : p4113 ∨ (¬ p4615))
    : p4113 ∨ (¬ p2383) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4113) := (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4615 := (Or.elim h73670 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h7365 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step78423 (p2307 p2317 p2321 : Prop)
    (h73242 : p2317 ∨ (¬ p2307))
    (h2772 : (¬ p2317) ∨ p2321)
    : (¬ p2307) ∨ p2321 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2321) := (fun h => hn (Or.inr h));
    let u2 : p2317 := (Or.elim h73242 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h2772 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step78424 (p2088 p2459 p3960 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h20316 : (¬ p2088) ∨ (¬ p3960) ∨ (¬ p4348))
    : p2459 ∨ (¬ p3960) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : p3960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h20316 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step78431 (p2088 p2528 p2534 p2553 p3573 p4170 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h71394 : (¬ p2088) ∨ (¬ p3573) ∨ (¬ p4170) ∨ (¬ p2553) ∨ (¬ p2534))
    : (¬ p2553) ∨ p2528 ∨ (¬ p3573) ∨ (¬ p4170) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71394 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78435 (p2088 p2166 p2528 p2534 p3696 p4607 p4632 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h55348 : (¬ p2088) ∨ (¬ p2166) ∨ (¬ p2534) ∨ (¬ p3696) ∨ (¬ p4607) ∨ (¬ p4632))
    : p2528 ∨ (¬ p3696) ∨ (¬ p2088) ∨ (¬ p4607) ∨ (¬ p4632) ∨ (¬ p2166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p3696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4607 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h55348 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step78446 (p2088 p2482 p2528 p2534 p2665 p3083 p4256 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73542 : p4256 ∨ p3083)
    (h48392 : (¬ p2088) ∨ (¬ p2482) ∨ (¬ p2534) ∨ (¬ p2665) ∨ (¬ p4256))
    : p2528 ∨ (¬ p2482) ∨ p3083 ∨ (¬ p2665) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p2482 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48392 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step78449 (p2088 p2482 p2509 p2528 p2534 p5194 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h49542 : (¬ p2088) ∨ (¬ p2482) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p5194))
    : p2528 ∨ (¬ p2482) ∨ (¬ p2088) ∨ (¬ p5194) ∨ (¬ p2509) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p2482 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49542 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step78451 (p2088 p2482 p2493 p2509 p2528 p2534 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h58564 : (¬ p2088) ∨ (¬ p2482) ∨ (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2534))
    : p2528 ∨ (¬ p2509) ∨ (¬ p2482) ∨ (¬ p2088) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2482 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h58564 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78452 (p2088 p2352 p2363 p2507 p3956 p4114 p4347 p5016 : Prop)
    (h73500 : p3956 ∨ p2352)
    (h73560 : p4347 ∨ p2363)
    (h59569 : (¬ p2088) ∨ (¬ p2507) ∨ (¬ p3956) ∨ (¬ p4114) ∨ (¬ p4347) ∨ (¬ p5016))
    : (¬ p4114) ∨ (¬ p5016) ∨ p2352 ∨ (¬ p2507) ∨ (¬ p2088) ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4114 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2507 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h59569 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step78456 (p2088 p2307 p2313 p2363 p4114 p4347 p4405 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73238 : p2313 ∨ p2307)
    (h41705 : (¬ p2088) ∨ (¬ p2313) ∨ (¬ p4114) ∨ (¬ p4347) ∨ (¬ p4405))
    : p2363 ∨ p2307 ∨ (¬ p4114) ∨ (¬ p4405) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4114 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41705 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step78458 (p2088 p2177 p2396 p4107 p4445 p4592 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h41129 : (¬ p2088) ∨ (¬ p2177) ∨ (¬ p4107) ∨ (¬ p4445) ∨ (¬ p4592))
    : p2396 ∨ (¬ p4592) ∨ (¬ p2177) ∨ (¬ p2088) ∨ (¬ p4445) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2396) := (fun h => hn (Or.inl h));
    let u1 : p4592 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41129 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step78461 (p2088 p2137 p2598 p2839 p2911 p2922 p2928 p3055 p3146 p3644 p3692 p4030 p4238 p4734 p4902 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73434 : p3644 ∨ p2911)
    (h73350 : p3055 ∨ p2598)
    (h73448 : p3692 ∨ p3146)
    (h72735 : p4734)
    (h63730 : (¬ p2088) ∨ (¬ p2137) ∨ (¬ p2839) ∨ (¬ p2928) ∨ (¬ p3055) ∨ (¬ p3644) ∨ (¬ p3692) ∨ (¬ p4030) ∨ (¬ p4238) ∨ (¬ p4734) ∨ (¬ p4902))
    : (¬ p4030) ∨ (¬ p2137) ∨ p2922 ∨ (¬ p2088) ∨ (¬ p4902) ∨ (¬ p4238) ∨ p2911 ∨ (¬ p2839) ∨ p2598 ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4030 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u13 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u14 : p4734 := h72735;
    (Or.elim h63730 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u14))) (fun r9 => (False.elim (r9 u4)))))))))))))))))))))))

theorem step78463 (p2088 p2528 p2534 p2881 p3960 p4186 p4277 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h41354 : (¬ p2088) ∨ (¬ p2534) ∨ (¬ p2881) ∨ (¬ p3960) ∨ (¬ p4186) ∨ (¬ p4277))
    : p2528 ∨ (¬ p2881) ∨ (¬ p4186) ∨ (¬ p2088) ∨ (¬ p4277) ∨ (¬ p3960) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4186 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41354 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step78468 (p2088 p2295 p2363 p3568 p3955 p4114 p4347 p4584 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73560 : p4347 ∨ p2363)
    (h49762 : (¬ p2088) ∨ (¬ p3568) ∨ (¬ p3955) ∨ (¬ p4114) ∨ (¬ p4347) ∨ (¬ p4584))
    : (¬ p4114) ∨ (¬ p2088) ∨ (¬ p4584) ∨ p2295 ∨ (¬ p3955) ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4114 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h49762 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step78469 (p2088 p2274 p2363 p3097 p3743 p4114 p4347 p4405 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73352 : p3097 ∨ p2274)
    (h41449 : (¬ p2088) ∨ (¬ p3097) ∨ (¬ p3743) ∨ (¬ p4114) ∨ (¬ p4347) ∨ (¬ p4405))
    : (¬ p4114) ∨ p2363 ∨ p2274 ∨ (¬ p4405) ∨ (¬ p3743) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4114 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41449 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step78470 (p2088 p2274 p2363 p3097 p3955 p4114 p4347 p4489 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73352 : p3097 ∨ p2274)
    (h51206 : (¬ p2088) ∨ (¬ p3097) ∨ (¬ p3955) ∨ (¬ p4114) ∨ (¬ p4347) ∨ (¬ p4489))
    : (¬ p4114) ∨ p2363 ∨ (¬ p3955) ∨ p2274 ∨ (¬ p4489) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4114 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4489 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h51206 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step78481 (p2088 p2363 p3857 p4170 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73479 : (¬ p2088) ∨ (¬ p3857))
    (h24461 : p3857 ∨ (¬ p4170) ∨ (¬ p4347))
    : p2363 ∨ (¬ p4170) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p4170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p3857) := (Or.elim h73479 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h24461 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step78487 (p2307 p2313 p3955 p4113 p4114 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h6141 : (¬ p2313) ∨ (¬ p3955) ∨ (¬ p4113) ∨ (¬ p4114))
    : (¬ p4114) ∨ (¬ p4113) ∨ (¬ p3955) ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4114 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4113 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h6141 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step78489 (p2088 p2254 p2707 p2881 p2901 p2946 p2952 p3537 p3570 p3609 p4114 p4242 p4320 p4340 p5020 : Prop)
    (h73538 : p4242 ∨ p3537)
    (h73330 : p2952 ∨ p2946)
    (h73552 : p4320 ∨ p2901)
    (h73418 : p3570 ∨ p2881)
    (h73558 : p4340 ∨ p3609)
    (h49057 : (¬ p2088) ∨ (¬ p2254) ∨ (¬ p2707) ∨ (¬ p2952) ∨ (¬ p3570) ∨ (¬ p4114) ∨ (¬ p4242) ∨ (¬ p4320) ∨ (¬ p4340) ∨ (¬ p5020))
    : p3537 ∨ (¬ p4114) ∨ (¬ p2254) ∨ (¬ p5020) ∨ p2946 ∨ p2901 ∨ p2881 ∨ p3609 ∨ (¬ p2707) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3537) := (fun h => hn (Or.inl h));
    let u1 : p4114 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4242 := (Or.elim h73538 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u14 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h49057 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u13))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u14))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step78491 (p2088 p2363 p3857 p4113 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h20071 : (¬ p2363) ∨ (¬ p3857) ∨ (¬ p4113))
    : (¬ p4113) ∨ p2088 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4113 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2088) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h20071 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u0)))))))

theorem step78495 (p2352 p2641 p3171 p3189 p3956 p4113 p4154 p4976 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73500 : p3956 ∨ p2352)
    (h59102 : (¬ p3171) ∨ (¬ p3189) ∨ (¬ p3956) ∨ (¬ p4113) ∨ (¬ p4154) ∨ (¬ p4976))
    : (¬ p4113) ∨ (¬ p3171) ∨ (¬ p3189) ∨ p2641 ∨ (¬ p4976) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4113 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4976 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h59102 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step78497 (p2088 p2510 p2528 p2553 p2588 p3857 p4113 p4405 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h73282 : p2588 ∨ p2553)
    (h41706 : (¬ p2510) ∨ (¬ p2528) ∨ (¬ p2588) ∨ (¬ p3857) ∨ (¬ p4113) ∨ (¬ p4405))
    : (¬ p2510) ∨ (¬ p4113) ∨ (¬ p4405) ∨ p2088 ∨ (¬ p2528) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2510 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4113 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41706 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step78500 (p2187 p2274 p2911 p3960 p3989 p4113 p4712 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h63201 : (¬ p2274) ∨ (¬ p2911) ∨ (¬ p3960) ∨ (¬ p3989) ∨ (¬ p4113) ∨ (¬ p4712))
    : (¬ p2911) ∨ (¬ p4113) ∨ (¬ p3960) ∨ (¬ p2274) ∨ (¬ p4712) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4113 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h63201 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step78503 (p2307 p2553 p2584 p2588 p2665 p3016 p3574 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73282 : p2588 ∨ p2553)
    (h51613 : (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p2665) ∨ (¬ p3574))
    : (¬ p2307) ∨ p3016 ∨ (¬ p2665) ∨ p2553 ∨ (¬ p2584) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h51613 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78511 (p2584 p3422 p3564 p3584 p3654 p4137 p4730 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h73426 : p3584 ∨ p3422)
    (h65012 : (¬ p2584) ∨ (¬ p3584) ∨ (¬ p3654) ∨ (¬ p4137) ∨ (¬ p4730))
    : (¬ p3654) ∨ p3564 ∨ p3422 ∨ (¬ p2584) ∨ (¬ p4730) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h65012 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step78515 (p2307 p2352 p2553 p2584 p2588 p2656 p2727 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h55351 : (¬ p2307) ∨ (¬ p2352) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p2656) ∨ (¬ p2727))
    : (¬ p2307) ∨ p2553 ∨ (¬ p2584) ∨ (¬ p2656) ∨ (¬ p2352) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h55351 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step78518 (p2307 p2493 p2499 p2553 p2584 p2588 p5194 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73260 : p2499 ∨ p2493)
    (h51610 : (¬ p2307) ∨ (¬ p2499) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p5194))
    : (¬ p2307) ∨ p2553 ∨ p2493 ∨ (¬ p2584) ∨ (¬ p5194) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h51610 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step78519 (p2307 p2470 p2476 p2553 p2584 p2588 p4595 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h73282 : p2588 ∨ p2553)
    (h41156 : (¬ p2307) ∨ (¬ p2476) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p4595))
    : (¬ p2307) ∨ p2470 ∨ (¬ p2584) ∨ (¬ p4595) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2470) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4595 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41156 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step78522 (p2584 p2590 p3389 p3540 p3564 p3654 p4137 p4644 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h73402 : p3540 ∨ p3389)
    (h51620 : (¬ p2584) ∨ (¬ p2590) ∨ (¬ p3540) ∨ (¬ p3654) ∨ (¬ p4137) ∨ (¬ p4644))
    : (¬ p3654) ∨ p3564 ∨ (¬ p2590) ∨ (¬ p2584) ∨ (¬ p4644) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h51620 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step78524 (p2230 p2307 p2553 p2584 p2588 p2589 p4717 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73284 : p2589 ∨ p2230)
    (h40920 : (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p2589) ∨ (¬ p4717))
    : (¬ p2307) ∨ p2553 ∨ (¬ p4717) ∨ p2230 ∨ (¬ p2584) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h40920 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step78525 (p2230 p2307 p2553 p2584 p2588 p2589 p4717 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73284 : p2589 ∨ p2230)
    (h48437 : (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p2589) ∨ (¬ p4717))
    : (¬ p2307) ∨ p2553 ∨ (¬ p2584) ∨ p2230 ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48437 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step78528 (p2573 p2578 p2582 : Prop)
    (h73275 : p2573 ∨ (¬ p2582))
    (h3287 : p2578 ∨ p2582)
    : p2578 ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2578) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2582) := (Or.elim h73275 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h3287 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step78539 (p2177 p2299 p2319 p2341 p2553 p2586 p2588 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73234 : p2299 ∨ p2177)
    (h40963 : (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2586) ∨ (¬ p2588))
    : (¬ p2341) ∨ (¬ p2319) ∨ (¬ p2586) ∨ p2553 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2586 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h40963 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78545 (p2319 p2341 p2911 p3644 p3654 p3946 p4620 p4710 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73492 : p3946 ∨ p3654)
    (h55846 : (¬ p2319) ∨ (¬ p2341) ∨ (¬ p3644) ∨ (¬ p3946) ∨ (¬ p4620) ∨ (¬ p4710))
    : (¬ p2319) ∨ (¬ p2341) ∨ (¬ p4710) ∨ p2911 ∨ p3654 ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55846 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step78546 (p2177 p2274 p2299 p2319 p2341 p3097 p4489 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h73352 : p3097 ∨ p2274)
    (h49217 : (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p3097) ∨ (¬ p4489))
    : (¬ p2341) ∨ (¬ p2319) ∨ (¬ p4489) ∨ p2177 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4489 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49217 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step78550 (p2319 p2383 p2387 p2396 p3516 p4107 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73246 : p2387 ∨ p2383)
    (h71396 : (¬ p3516) ∨ (¬ p2387) ∨ (¬ p2319) ∨ (¬ p4107))
    : (¬ p3516) ∨ (¬ p2319) ∨ p2396 ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71396 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78552 (p2177 p2295 p2299 p2319 p2341 p3568 p4584 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73234 : p2299 ∨ p2177)
    (h49252 : (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p3568) ∨ (¬ p4584))
    : (¬ p2341) ∨ p2295 ∨ (¬ p4584) ∨ p2177 ∨ (¬ p2319) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49252 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step78555 (p2319 p2341 p2437 p2584 p2665 p2911 p3644 p3742 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73434 : p3644 ∨ p2911)
    (h60107 : (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2584) ∨ (¬ p2665) ∨ (¬ p3644) ∨ (¬ p3742))
    : (¬ p2341) ∨ p2437 ∨ (¬ p2319) ∨ (¬ p2584) ∨ p2911 ∨ (¬ p2665) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h60107 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step78559 (p2177 p2319 p2396 p2797 p3516 p3567 p4107 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h45771 : (¬ p2177) ∨ (¬ p2319) ∨ (¬ p2797) ∨ (¬ p3516) ∨ (¬ p3567) ∨ (¬ p4107))
    : (¬ p3516) ∨ p2396 ∨ (¬ p2177) ∨ (¬ p2319) ∨ (¬ p2797) ∨ (¬ p3567) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45771 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step78562 (p2177 p2299 p2319 p2341 p2578 p2850 p3422 p3684 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73234 : p2299 ∨ p2177)
    (h48387 : (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2578) ∨ (¬ p3422) ∨ (¬ p3684))
    : (¬ p2341) ∨ (¬ p2319) ∨ p2850 ∨ p2177 ∨ (¬ p2578) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48387 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step78564 (p2319 p2352 p2383 p2387 p2901 p3660 p4283 p4320 p4702 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73246 : p2387 ∨ p2383)
    (h60677 : (¬ p2319) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p3660) ∨ (¬ p4283) ∨ (¬ p4320) ∨ (¬ p4702))
    : p2901 ∨ (¬ p2319) ∨ (¬ p3660) ∨ (¬ p4702) ∨ (¬ p4283) ∨ p2383 ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h60677 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step78571 (p2318 p2396 p3516 p3821 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h6142 : (¬ p2318) ∨ (¬ p2396) ∨ (¬ p3821))
    : (¬ p2318) ∨ p3516 ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2318 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3516) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h6142 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step78583 (p2318 p2341 p2507 p2553 p2588 p3527 p3551 p4452 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73282 : p2588 ∨ p2553)
    (h41220 : (¬ p2318) ∨ (¬ p2507) ∨ (¬ p2588) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p4452))
    : (¬ p3527) ∨ (¬ p4452) ∨ p2341 ∨ (¬ p2318) ∨ p2553 ∨ (¬ p2507) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2318 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2507 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41220 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step78585 (p2187 p2318 p3246 p3516 p3821 p3872 p3989 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73502 : p3989 ∨ p2187)
    (h71398 : (¬ p3821) ∨ (¬ p3246) ∨ (¬ p3989) ∨ (¬ p2318) ∨ (¬ p3872))
    : p3516 ∨ (¬ p3246) ∨ p2187 ∨ (¬ p2318) ∨ (¬ p3872) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2318 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h71398 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step78586 (p2122 p2318 p2341 p2911 p3551 p3822 p3920 p5222 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73472 : p3822 ∨ p2122)
    (h42286 : (¬ p2318) ∨ (¬ p2911) ∨ (¬ p3551) ∨ (¬ p3822) ∨ (¬ p3920) ∨ (¬ p5222))
    : (¬ p2318) ∨ p2341 ∨ p2122 ∨ (¬ p3920) ∨ (¬ p2911) ∨ (¬ p5222) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2318 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3920 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42286 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step78587 (p2248 p2284 p2509 p2528 p2534 p2946 p3125 p3379 p3452 p4330 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73268 : p2534 ∨ p2528)
    (h48477 : (¬ p2248) ∨ (¬ p2284) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p3452) ∨ (¬ p4330))
    : p3379 ∨ (¬ p2248) ∨ (¬ p3125) ∨ (¬ p2509) ∨ p2528 ∨ (¬ p2284) ∨ (¬ p4330) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48477 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step78588 (p2187 p2274 p3097 p3955 p3989 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73501 : (¬ p2187) ∨ (¬ p3989))
    (h6629 : (¬ p3097) ∨ (¬ p3955) ∨ p3989)
    : p2274 ∨ (¬ p2187) ∨ (¬ p3955) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p3989) := (Or.elim h73501 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h6629 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u4 r1)))))))

theorem step78592 (p2363 p4171 p4600 : Prop)
    (h73660 : p4600 ∨ p2363)
    (h7325 : p4171 ∨ (¬ p4600))
    : p4171 ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4171) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr h));
    let u2 : p4600 := (Or.elim h73660 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h7325 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step78593 (p2363 p4600 p4601 : Prop)
    (h73660 : p4600 ∨ p2363)
    (h7327 : (¬ p4600) ∨ p4601)
    : p2363 ∨ p4601 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4601) := (fun h => hn (Or.inr h));
    let u2 : p4600 := (Or.elim h73660 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7327 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step78594 (p2363 p4330 p4600 : Prop)
    (h73660 : p4600 ∨ p2363)
    (h7328 : p4330 ∨ (¬ p4600))
    : p4330 ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4330) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr h));
    let u2 : p4600 := (Or.elim h73660 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h7328 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step78595 (p2177 p3955 p4500 : Prop)
    (h73602 : p4500 ∨ p2177)
    (h7054 : p3955 ∨ (¬ p4500))
    : p3955 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3955) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2177) := (fun h => hn (Or.inr h));
    let u2 : p4500 := (Or.elim h73602 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h7054 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step78596 (p2177 p3955 p5797 : Prop)
    (h74073 : p2177 ∨ (¬ p5797))
    (h11785 : p3955 ∨ p5797)
    : p3955 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3955) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2177) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5797) := (Or.elim h74073 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11785 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step78597 (p2187 p2363 p2528 p2534 p3573 p3958 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h52522 : (¬ p2187) ∨ (¬ p2363) ∨ (¬ p2534) ∨ (¬ p3573) ∨ (¬ p3958))
    : (¬ p2187) ∨ (¬ p3573) ∨ (¬ p3958) ∨ (¬ p2363) ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h52522 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step78599 (p2187 p2331 p2363 p2946 p2952 p3986 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h43519 : (¬ p2187) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2952) ∨ (¬ p3986))
    : (¬ p2331) ∨ (¬ p2187) ∨ (¬ p3986) ∨ (¬ p2363) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43519 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step78608 (p2284 p2960 p2962 p3125 p3654 p3744 p3952 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h73496 : p3952 ∨ p2284)
    (h60750 : (¬ p2960) ∨ (¬ p2962) ∨ (¬ p3654) ∨ (¬ p3744) ∨ (¬ p3952))
    : (¬ p3654) ∨ p3125 ∨ (¬ p2960) ∨ p2284 ∨ (¬ p2962) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60750 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step78609 (p2187 p2383 p2962 p3051 p3556 p3989 p4555 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73502 : p3989 ∨ p2187)
    (h41809 : (¬ p2383) ∨ (¬ p2962) ∨ (¬ p3556) ∨ (¬ p3989) ∨ (¬ p4555))
    : p3051 ∨ (¬ p2383) ∨ (¬ p2962) ∨ (¬ p4555) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41809 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step78611 (p2274 p2440 p2542 p2962 p3125 p3654 p3744 p4109 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h73270 : p2542 ∨ p2440)
    (h52640 : (¬ p2274) ∨ (¬ p2542) ∨ (¬ p2962) ∨ (¬ p3654) ∨ (¬ p3744) ∨ (¬ p4109))
    : (¬ p3654) ∨ p3125 ∨ (¬ p2274) ∨ (¬ p2962) ∨ p2440 ∨ (¬ p4109) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h52640 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step78614 (p2137 p2274 p2307 p2962 p3097 p3105 p4385 p5043 : Prop)
    (h73576 : p4385 ∨ p3105)
    (h73352 : p3097 ∨ p2274)
    (h56906 : (¬ p2137) ∨ (¬ p2307) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p4385) ∨ (¬ p5043))
    : (¬ p2307) ∨ (¬ p2137) ∨ (¬ p5043) ∨ p3105 ∨ (¬ p2962) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3105) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4385 := (Or.elim h73576 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h56906 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step78621 (p2352 p2363 p2573 p2946 p2952 p3136 p3366 p3519 p3755 p4035 p4236 p4376 p5113 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73506 : p4035 ∨ p3755)
    (h54867 : (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p4035) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p5113))
    : (¬ p2573) ∨ (¬ p2352) ∨ (¬ p3366) ∨ p2946 ∨ (¬ p4376) ∨ (¬ p3136) ∨ (¬ p5113) ∨ (¬ p4236) ∨ p3755 ∨ (¬ p3519) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5113 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h54867 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u4))) (fun r9 => (False.elim (r9 u6)))))))))))))))))))))))

theorem step78622 (p2352 p2363 p3146 p3692 p3988 p4718 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h41319 : (¬ p2352) ∨ (¬ p2363) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4718))
    : (¬ p2352) ∨ p3146 ∨ (¬ p2363) ∨ (¬ p4718) ∨ (¬ p3988) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41319 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step78623 (p2352 p2363 p2459 p2553 p2588 p4348 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73562 : p4348 ∨ p2459)
    (h47453 : (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2588) ∨ (¬ p4348))
    : (¬ p2352) ∨ p2553 ∨ p2459 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47453 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step78634 (p2187 p2383 p3743 p3989 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h19844 : (¬ p2383) ∨ (¬ p3743) ∨ (¬ p3989))
    : (¬ p2383) ∨ (¬ p3743) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h19844 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step78636 (p2284 p2383 p2901 p3743 p4275 p4320 p4405 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h60047 : (¬ p2284) ∨ (¬ p2383) ∨ (¬ p3743) ∨ (¬ p4275) ∨ (¬ p4320) ∨ (¬ p4405))
    : p2901 ∨ (¬ p2383) ∨ (¬ p3743) ∨ (¬ p2284) ∨ (¬ p4405) ∨ (¬ p4275) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h60047 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step78638 (p2284 p2307 p2504 p2590 p3309 p3549 p3743 p4705 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h41167 : (¬ p2284) ∨ (¬ p2307) ∨ (¬ p2504) ∨ (¬ p2590) ∨ (¬ p3549) ∨ (¬ p3743) ∨ (¬ p4705))
    : (¬ p2307) ∨ p3309 ∨ (¬ p2284) ∨ (¬ p2590) ∨ (¬ p3743) ∨ (¬ p4705) ∨ (¬ p2504) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3309) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41167 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step78641 (p2284 p2590 p3564 p3654 p3743 p4137 p4705 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h54329 : (¬ p2284) ∨ (¬ p2590) ∨ (¬ p3654) ∨ (¬ p3743) ∨ (¬ p4137) ∨ (¬ p4705))
    : (¬ p3654) ∨ (¬ p3743) ∨ (¬ p2284) ∨ p3564 ∨ (¬ p4705) ∨ (¬ p2590) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54329 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step78642 (p3125 p3743 p3744 p4036 p4038 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h39332 : (¬ p3743) ∨ (¬ p3744) ∨ (¬ p4036) ∨ (¬ p4038))
    : (¬ p4036) ∨ (¬ p4038) ∨ (¬ p3743) ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4036 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4038 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h39332 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step78644 (p2284 p2319 p2341 p2441 p2911 p3644 p3743 p4705 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h54384 : (¬ p2284) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2441) ∨ (¬ p3644) ∨ (¬ p3743) ∨ (¬ p4705))
    : (¬ p2341) ∨ (¬ p3743) ∨ (¬ p4705) ∨ (¬ p2284) ∨ p2911 ∨ (¬ p2441) ∨ (¬ p2319) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54384 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step78645 (p2295 p2383 p2563 p2668 p3324 p3743 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h43289 : (¬ p2295) ∨ (¬ p2383) ∨ (¬ p2563) ∨ (¬ p3324) ∨ (¬ p3743))
    : (¬ p2295) ∨ (¬ p2383) ∨ p2668 ∨ (¬ p2563) ∨ (¬ p3743) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43289 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step78646 (p2295 p2383 p2668 p2860 p3324 p3743 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h43208 : (¬ p2295) ∨ (¬ p2383) ∨ (¬ p2860) ∨ (¬ p3324) ∨ (¬ p3743))
    : (¬ p2295) ∨ (¬ p2383) ∨ p2668 ∨ (¬ p2860) ∨ (¬ p3743) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43208 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step78647 (p2307 p2373 p2553 p2588 p2590 p3743 p4509 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h41172 : (¬ p2307) ∨ (¬ p2373) ∨ (¬ p2588) ∨ (¬ p2590) ∨ (¬ p3743) ∨ (¬ p4509))
    : (¬ p2307) ∨ (¬ p3743) ∨ p2553 ∨ (¬ p4509) ∨ (¬ p2590) ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41172 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step78650 (p2187 p2363 p2510 p2528 p3989 p4347 p4718 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73502 : p3989 ∨ p2187)
    (h51167 : (¬ p2510) ∨ (¬ p2528) ∨ (¬ p3989) ∨ (¬ p4347) ∨ (¬ p4718))
    : (¬ p2528) ∨ (¬ p2510) ∨ p2363 ∨ (¬ p4718) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2510 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51167 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step78651 (p2295 p2668 p3324 p3568 p3955 : Prop)
    (h73385 : (¬ p2668) ∨ (¬ p3324))
    (h73416 : p3568 ∨ p2295)
    (h30369 : p3324 ∨ (¬ p3568) ∨ (¬ p3955))
    : (¬ p2668) ∨ p2295 ∨ (¬ p3955) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3324) := (Or.elim h73385 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h30369 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u2)))))))

theorem step78653 (p2187 p2668 p3324 p3745 p3989 : Prop)
    (h73385 : (¬ p2668) ∨ (¬ p3324))
    (h73502 : p3989 ∨ p2187)
    (h22989 : p3324 ∨ (¬ p3745) ∨ (¬ p3989))
    : (¬ p2668) ∨ (¬ p3745) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3324) := (Or.elim h73385 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h22989 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step78655 (p2352 p2668 p3324 p3956 p4389 : Prop)
    (h73385 : (¬ p2668) ∨ (¬ p3324))
    (h73500 : p3956 ∨ p2352)
    (h6828 : p3324 ∨ (¬ p3956) ∨ (¬ p4389))
    : (¬ p4389) ∨ (¬ p2668) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3324) := (Or.elim h73385 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u4 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h6828 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u0)))))))

theorem step78662 (p2274 p2295 p3097 p3568 p3745 : Prop)
    (h73415 : (¬ p2295) ∨ (¬ p3568))
    (h73352 : p3097 ∨ p2274)
    (h6933 : (¬ p3097) ∨ p3568 ∨ (¬ p3745))
    : (¬ p2295) ∨ (¬ p3745) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3568) := (Or.elim h73415 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h6933 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step78664 (p2295 p3323 p3568 p4037 p4187 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73415 : (¬ p2295) ∨ (¬ p3568))
    (h25216 : p3568 ∨ (¬ p4037) ∨ (¬ p4187))
    : (¬ p4187) ∨ p3323 ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : (¬ p3568) := (Or.elim h73415 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h25216 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u0)))))))

theorem step78666 (p2295 p2668 p3324 p3325 p3568 : Prop)
    (h73415 : (¬ p2295) ∨ (¬ p3568))
    (h73386 : p3324 ∨ p2668)
    (h26890 : (¬ p3324) ∨ (¬ p3325) ∨ p3568)
    : (¬ p2295) ∨ (¬ p3325) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3568) := (Or.elim h73415 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h26890 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u3 r1)))))))

theorem step78668 (p2295 p2307 p2313 p2667 p3568 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73415 : (¬ p2295) ∨ (¬ p3568))
    (h33740 : (¬ p2313) ∨ (¬ p2667) ∨ p3568)
    : p2307 ∨ (¬ p2295) ∨ (¬ p2667) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2307) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p3568) := (Or.elim h73415 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h33740 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u4 r1)))))))

theorem step78671 (p2187 p4508 p4509 : Prop)
    (h73608 : p4508 ∨ (¬ p2187))
    (h7080 : (¬ p4508) ∨ p4509)
    : (¬ p2187) ∨ p4509 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4509) := (fun h => hn (Or.inr h));
    let u2 : p4508 := (Or.elim h73608 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h7080 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step78672 (p2187 p4134 p4508 : Prop)
    (h73608 : p4508 ∨ (¬ p2187))
    (h7081 : p4134 ∨ (¬ p4508))
    : p4134 ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4134) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4508 := (Or.elim h73608 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h7081 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step78674 (p2363 p3146 p3692 p4347 p4506 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73447 : (¬ p3146) ∨ (¬ p3692))
    (h23451 : p3692 ∨ (¬ p4347) ∨ (¬ p4506))
    : p2363 ∨ (¬ p3146) ∨ (¬ p4506) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p3692) := (Or.elim h73447 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h23451 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step78678 (p2220 p2363 p2440 p2542 p3146 p4109 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73270 : p2542 ∨ p2440)
    (h62431 : (¬ p2220) ∨ (¬ p2542) ∨ (¬ p3146) ∨ (¬ p4109) ∨ (¬ p4347))
    : (¬ p3146) ∨ p2363 ∨ (¬ p4109) ∨ (¬ p2220) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62431 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78680 (p2528 p2534 p2619 p2860 p3146 p3758 : Prop)
    (h73456 : p3758 ∨ p2860)
    (h73268 : p2534 ∨ p2528)
    (h43743 : (¬ p2534) ∨ (¬ p2619) ∨ (¬ p3146) ∨ (¬ p3758))
    : (¬ p2619) ∨ p2860 ∨ p2528 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2860) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43743 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78682 (p2156 p2373 p2563 p3146 p4110 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h53409 : (¬ p2156) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p4110))
    : (¬ p2373) ∨ (¬ p2156) ∨ p2563 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h53409 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78688 (p2132 p2166 p2449 p2737 p2743 p2807 p3146 p3361 p3414 p3947 p4418 p4669 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73392 : p3414 ∨ p2807)
    (h73298 : p2743 ∨ p2737)
    (h71400 : (¬ p4418) ∨ (¬ p3146) ∨ (¬ p2132) ∨ (¬ p2743) ∨ (¬ p3947) ∨ (¬ p3414) ∨ (¬ p2166) ∨ (¬ p4669) ∨ (¬ p3361))
    : p2449 ∨ (¬ p4418) ∨ p2807 ∨ p2737 ∨ (¬ p3146) ∨ (¬ p2132) ∨ (¬ p3361) ∨ (¬ p4669) ∨ (¬ p2166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71400 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step78696 (p2220 p2459 p2951 p2992 p3146 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h56400 : (¬ p2220) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3146) ∨ (¬ p4348))
    : (¬ p2951) ∨ (¬ p3146) ∨ (¬ p2220) ∨ p2459 ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2951 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56400 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78699 (p2440 p2528 p2534 p2542 p3083 p3146 p4256 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73542 : p4256 ∨ p3083)
    (h73270 : p2542 ∨ p2440)
    (h46008 : (¬ p2534) ∨ (¬ p2542) ∨ (¬ p3146) ∨ (¬ p4256))
    : p2528 ∨ p3083 ∨ (¬ p3146) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46008 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step78700 (p2470 p2476 p2528 p2534 p2662 p2727 p3146 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73268 : p2534 ∨ p2528)
    (h73250 : p2476 ∨ p2470)
    (h43589 : (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2662) ∨ (¬ p3146) ∨ (¬ p4111))
    : p2727 ∨ p2528 ∨ (¬ p2662) ∨ (¬ p3146) ∨ p2470 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43589 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78701 (p2230 p2470 p2476 p2528 p2534 p3146 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73250 : p2476 ∨ p2470)
    (h61785 : (¬ p2230) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3146))
    : (¬ p2230) ∨ p2528 ∨ p2470 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h61785 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step78703 (p2264 p2470 p2476 p2528 p2534 p2685 p2696 p3146 p4108 p4733 p4905 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73250 : p2476 ∨ p2470)
    (h56338 : (¬ p2264) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3146) ∨ (¬ p4108) ∨ (¬ p4733) ∨ (¬ p4905))
    : p2528 ∨ (¬ p2264) ∨ (¬ p4905) ∨ (¬ p4108) ∨ (¬ p2696) ∨ (¬ p3146) ∨ p2470 ∨ (¬ p2685) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h56338 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step78704 (p2470 p2476 p2528 p2534 p3146 p3389 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h73268 : p2534 ∨ p2528)
    (h54258 : (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3146) ∨ (¬ p3389))
    : p2470 ∨ p2528 ∨ (¬ p3389) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2470) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h54258 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step78705 (p2220 p2427 p3051 p3146 p3556 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h61036 : (¬ p2220) ∨ (¬ p2427) ∨ (¬ p3146) ∨ (¬ p3556))
    : p3051 ∨ (¬ p2220) ∨ (¬ p3146) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h61036 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78707 (p2230 p2528 p2534 p2589 p2608 p2630 p2662 p2707 p2717 p2810 p3146 p4607 p4905 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73284 : p2589 ∨ p2230)
    (h73316 : p2810 ∨ p2630)
    (h60853 : (¬ p2534) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2662) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p2810) ∨ (¬ p3146) ∨ (¬ p4607) ∨ (¬ p4905))
    : p2528 ∨ (¬ p2608) ∨ p2230 ∨ (¬ p3146) ∨ (¬ p2717) ∨ (¬ p4905) ∨ (¬ p4607) ∨ (¬ p2707) ∨ p2630 ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4607 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h60853 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step78710 (p2156 p2220 p2459 p3146 p3646 p4348 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73562 : p4348 ∨ p2459)
    (h63785 : (¬ p2220) ∨ (¬ p3146) ∨ (¬ p3646) ∨ (¬ p4348))
    : (¬ p2220) ∨ p2156 ∨ p2459 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h63785 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step78712 (p2220 p2352 p2459 p2493 p2499 p3146 p3379 p3452 p3956 p4348 p4503 p4521 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73562 : p4348 ∨ p2459)
    (h73394 : p3452 ∨ p3379)
    (h73500 : p3956 ∨ p2352)
    (h54117 : (¬ p2220) ∨ (¬ p2499) ∨ (¬ p3146) ∨ (¬ p3452) ∨ (¬ p3956) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4521))
    : (¬ p2220) ∨ (¬ p4503) ∨ p2493 ∨ (¬ p3146) ∨ p2459 ∨ p3379 ∨ (¬ p4521) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h54117 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step78714 (p2284 p2459 p3146 p3156 p3952 p4348 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73562 : p4348 ∨ p2459)
    (h55793 : (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3952) ∨ (¬ p4348))
    : (¬ p3156) ∨ p2284 ∨ p2459 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h55793 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step78715 (p2230 p2427 p2459 p3146 p3747 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h46729 : (¬ p2230) ∨ (¬ p2427) ∨ (¬ p3146) ∨ (¬ p3747) ∨ (¬ p4348))
    : (¬ p2427) ∨ (¬ p3747) ∨ p2459 ∨ (¬ p2230) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46729 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78717 (p2254 p2608 p2707 p2717 p3146 p3166 p3172 p3256 p4118 p4905 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h73520 : p4118 ∨ p3256)
    (h48676 : (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p3146) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4905))
    : p3166 ∨ p3256 ∨ (¬ p2254) ∨ (¬ p2707) ∨ (¬ p4905) ∨ (¬ p2608) ∨ (¬ p2717) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h48676 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step78721 (p2156 p2220 p2860 p3146 p3646 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h53909 : (¬ p2220) ∨ (¬ p2860) ∨ (¬ p3146) ∨ (¬ p3646))
    : (¬ p2220) ∨ p2156 ∨ (¬ p2860) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h53909 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

end ElevenRUP
