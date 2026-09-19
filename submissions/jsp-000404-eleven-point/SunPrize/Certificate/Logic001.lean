import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step41409 (p2027 p2373 p2406 p3904 p4120 p5191 : Prop)
    (h40810 : (¬ p2027))
    (h10278 : p2027 ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p3904) ∨ (¬ p4120) ∨ (¬ p5191))
    : (¬ p2373) ∨ (¬ p2406) ∨ (¬ p3904) ∨ (¬ p4120) ∨ (¬ p5191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10278 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41410 (p2027 p2373 p2387 p4110 p4441 p4486 : Prop)
    (h40810 : (¬ p2027))
    (h10279 : p2027 ∨ (¬ p2373) ∨ (¬ p2387) ∨ (¬ p4110) ∨ (¬ p4441) ∨ (¬ p4486))
    : (¬ p2373) ∨ (¬ p2387) ∨ (¬ p4110) ∨ (¬ p4441) ∨ (¬ p4486) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10279 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41411 (p2027 p2774 p3365 p3367 p3688 p4752 : Prop)
    (h40810 : (¬ p2027))
    (h10280 : p2027 ∨ (¬ p2774) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p4752))
    : (¬ p2774) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p4752) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2774 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10280 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41413 (p2027 p2532 p2982 p3880 p4348 p4905 : Prop)
    (h40810 : (¬ p2027))
    (h10283 : p2027 ∨ (¬ p2532) ∨ (¬ p2982) ∨ (¬ p3880) ∨ (¬ p4348) ∨ (¬ p4905))
    : (¬ p2532) ∨ (¬ p2982) ∨ (¬ p3880) ∨ (¬ p4348) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2532 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10283 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41415 (p2027 p2088 p2274 p2312 p4261 p4371 p4514 p4590 : Prop)
    (h40810 : (¬ p2027))
    (h10285 : p2027 ∨ (¬ p2088) ∨ (¬ p2274) ∨ (¬ p2312) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p4514) ∨ (¬ p4590))
    : (¬ p2088) ∨ (¬ p2274) ∨ (¬ p2312) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p4514) ∨ (¬ p4590) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h10285 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41416 (p2027 p2295 p3093 p4366 p4427 p4757 : Prop)
    (h40810 : (¬ p2027))
    (h10286 : p2027 ∨ (¬ p2295) ∨ (¬ p3093) ∨ (¬ p4366) ∨ (¬ p4427) ∨ (¬ p4757))
    : (¬ p2295) ∨ (¬ p3093) ∨ (¬ p4366) ∨ (¬ p4427) ∨ (¬ p4757) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4757 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10286 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41417 (p2027 p2313 p2501 p2553 p3093 p5015 : Prop)
    (h40810 : (¬ p2027))
    (h10287 : p2027 ∨ (¬ p2313) ∨ (¬ p2501) ∨ (¬ p2553) ∨ (¬ p3093) ∨ (¬ p5015))
    : (¬ p2313) ∨ (¬ p2501) ∨ (¬ p2553) ∨ (¬ p3093) ∨ (¬ p5015) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5015 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10287 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41419 (p2027 p2187 p2331 p3172 p4564 p4769 : Prop)
    (h40810 : (¬ p2027))
    (h10289 : p2027 ∨ (¬ p2187) ∨ (¬ p2331) ∨ (¬ p3172) ∨ (¬ p4564) ∨ (¬ p4769))
    : (¬ p2187) ∨ (¬ p2331) ∨ (¬ p3172) ∨ (¬ p4564) ∨ (¬ p4769) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4769 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10289 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41421 (p2027 p3564 p3857 p3956 p4345 p4614 : Prop)
    (h40810 : (¬ p2027))
    (h10291 : p2027 ∨ (¬ p3564) ∨ (¬ p3857) ∨ (¬ p3956) ∨ (¬ p4345) ∨ (¬ p4614))
    : (¬ p3564) ∨ (¬ p3857) ∨ (¬ p3956) ∨ (¬ p4345) ∨ (¬ p4614) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4345 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4614 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10291 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41422 (p2027 p2253 p2331 p2750 p3954 p4154 : Prop)
    (h40810 : (¬ p2027))
    (h10292 : p2027 ∨ (¬ p2253) ∨ (¬ p2331) ∨ (¬ p2750) ∨ (¬ p3954) ∨ (¬ p4154))
    : (¬ p2253) ∨ (¬ p2331) ∨ (¬ p2750) ∨ (¬ p3954) ∨ (¬ p4154) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2253 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10292 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41423 (p2027 p2274 p2311 p2396 p3821 p4486 : Prop)
    (h40810 : (¬ p2027))
    (h10293 : p2027 ∨ (¬ p2274) ∨ (¬ p2311) ∨ (¬ p2396) ∨ (¬ p3821) ∨ (¬ p4486))
    : (¬ p2274) ∨ (¬ p2311) ∨ (¬ p2396) ∨ (¬ p3821) ∨ (¬ p4486) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10293 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41424 (p2027 p2298 p2553 p2797 p3572 p4973 : Prop)
    (h40810 : (¬ p2027))
    (h10294 : p2027 ∨ (¬ p2298) ∨ (¬ p2553) ∨ (¬ p2797) ∨ (¬ p3572) ∨ (¬ p4973))
    : (¬ p2298) ∨ (¬ p2553) ∨ (¬ p2797) ∨ (¬ p3572) ∨ (¬ p4973) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2298 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10294 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41425 (p2027 p2352 p2387 p2577 p3389 p4711 : Prop)
    (h40810 : (¬ p2027))
    (h10295 : p2027 ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2577) ∨ (¬ p3389) ∨ (¬ p4711))
    : (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2577) ∨ (¬ p3389) ∨ (¬ p4711) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4711 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10295 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41427 (p2027 p2166 p2751 p3497 p4315 p4365 : Prop)
    (h40810 : (¬ p2027))
    (h10297 : p2027 ∨ (¬ p2166) ∨ (¬ p2751) ∨ (¬ p3497) ∨ (¬ p4315) ∨ (¬ p4365))
    : (¬ p2166) ∨ (¬ p2751) ∨ (¬ p3497) ∨ (¬ p4315) ∨ (¬ p4365) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10297 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41428 (p2027 p2727 p2749 p2810 p3583 p5049 : Prop)
    (h40810 : (¬ p2027))
    (h10298 : p2027 ∨ (¬ p2727) ∨ (¬ p2749) ∨ (¬ p2810) ∨ (¬ p3583) ∨ (¬ p5049))
    : (¬ p2727) ∨ (¬ p2749) ∨ (¬ p2810) ∨ (¬ p3583) ∨ (¬ p5049) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5049 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10298 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41429 (p2027 p2870 p3698 p4129 p4382 p4830 p4948 : Prop)
    (h40810 : (¬ p2027))
    (h10299 : p2027 ∨ (¬ p2870) ∨ (¬ p3698) ∨ (¬ p4129) ∨ (¬ p4382) ∨ (¬ p4830) ∨ (¬ p4948))
    : (¬ p2870) ∨ (¬ p3698) ∨ (¬ p4129) ∨ (¬ p4382) ∨ (¬ p4830) ∨ (¬ p4948) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4129 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4382 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10299 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41430 (p2027 p3670 p4037 p4191 p4231 p4846 : Prop)
    (h40810 : (¬ p2027))
    (h10300 : p2027 ∨ (¬ p3670) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4231) ∨ (¬ p4846))
    : (¬ p3670) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4231) ∨ (¬ p4846) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3670 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4231 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4846 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10300 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41432 (p2027 p2249 p2284 p2950 p2992 p3646 : Prop)
    (h40810 : (¬ p2027))
    (h10302 : p2027 ∨ (¬ p2249) ∨ (¬ p2284) ∨ (¬ p2950) ∨ (¬ p2992) ∨ (¬ p3646))
    : (¬ p2249) ∨ (¬ p2284) ∨ (¬ p2950) ∨ (¬ p2992) ∨ (¬ p3646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2249 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10302 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41435 (p2027 p2315 p2363 p3325 p3551 p4348 : Prop)
    (h40810 : (¬ p2027))
    (h10305 : p2027 ∨ (¬ p2315) ∨ (¬ p2363) ∨ (¬ p3325) ∨ (¬ p3551) ∨ (¬ p4348))
    : (¬ p2315) ∨ (¬ p2363) ∨ (¬ p3325) ∨ (¬ p3551) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2315 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10305 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41436 (p2027 p2137 p2156 p2839 p3588 p4169 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h10306 : p2027 ∨ (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2839) ∨ (¬ p3588) ∨ (¬ p4169) ∨ (¬ p4555))
    : (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2839) ∨ (¬ p3588) ∨ (¬ p4169) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2137 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4169 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10306 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41437 (p2027 p2295 p2312 p2341 p3324 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h10307 : p2027 ∨ (¬ p2295) ∨ (¬ p2312) ∨ (¬ p2341) ∨ (¬ p3324) ∨ (¬ p4503))
    : (¬ p2295) ∨ (¬ p2312) ∨ (¬ p2341) ∨ (¬ p3324) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10307 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41438 (p2027 p2104 p2696 p2751 p3189 p4963 : Prop)
    (h40810 : (¬ p2027))
    (h10308 : p2027 ∨ (¬ p2104) ∨ (¬ p2696) ∨ (¬ p2751) ∨ (¬ p3189) ∨ (¬ p4963))
    : (¬ p2104) ∨ (¬ p2696) ∨ (¬ p2751) ∨ (¬ p3189) ∨ (¬ p4963) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10308 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41440 (p2027 p2528 p3166 p3292 p5009 p5107 : Prop)
    (h40810 : (¬ p2027))
    (h10310 : p2027 ∨ (¬ p2528) ∨ (¬ p3166) ∨ (¬ p3292) ∨ (¬ p5009) ∨ (¬ p5107))
    : (¬ p2528) ∨ (¬ p3166) ∨ (¬ p3292) ∨ (¬ p5009) ∨ (¬ p5107) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3292 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5009 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10310 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41441 (p2027 p2685 p3552 p4037 p4195 p4620 : Prop)
    (h40810 : (¬ p2027))
    (h10311 : p2027 ∨ (¬ p2685) ∨ (¬ p3552) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p4620))
    : (¬ p2685) ∨ (¬ p3552) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2685 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3552 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10311 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41442 (p2027 p2751 p2972 p4208 p4315 p4365 : Prop)
    (h40810 : (¬ p2027))
    (h10313 : p2027 ∨ (¬ p2751) ∨ (¬ p2972) ∨ (¬ p4208) ∨ (¬ p4315) ∨ (¬ p4365))
    : (¬ p2751) ∨ (¬ p2972) ∨ (¬ p4208) ∨ (¬ p4315) ∨ (¬ p4365) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2751 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10313 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41443 (p2027 p2493 p2751 p2810 p3574 p4281 : Prop)
    (h40810 : (¬ p2027))
    (h10314 : p2027 ∨ (¬ p2493) ∨ (¬ p2751) ∨ (¬ p2810) ∨ (¬ p3574) ∨ (¬ p4281))
    : (¬ p2493) ∨ (¬ p2751) ∨ (¬ p2810) ∨ (¬ p3574) ∨ (¬ p4281) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10314 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41444 (p2027 p2751 p3027 p3516 p4066 p4324 p4781 : Prop)
    (h40810 : (¬ p2027))
    (h10315 : p2027 ∨ (¬ p2751) ∨ (¬ p3027) ∨ (¬ p3516) ∨ (¬ p4066) ∨ (¬ p4324) ∨ p4781)
    : (¬ p2751) ∨ (¬ p3027) ∨ (¬ p3516) ∨ (¬ p4066) ∨ (¬ p4324) ∨ p4781 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2751 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p4781) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10315 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (u5 r5)))))))))))))))

theorem step41445 (p2027 p2751 p3319 p4037 p4195 p4759 : Prop)
    (h40810 : (¬ p2027))
    (h10316 : p2027 ∨ (¬ p2751) ∨ (¬ p3319) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p4759))
    : (¬ p2751) ∨ (¬ p3319) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p4759) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2751 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10316 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41446 (p2027 p2307 p2751 p3568 p4195 p4759 p5016 : Prop)
    (h40810 : (¬ p2027))
    (h10317 : p2027 ∨ (¬ p2307) ∨ (¬ p2751) ∨ (¬ p3568) ∨ (¬ p4195) ∨ (¬ p4759) ∨ (¬ p5016))
    : (¬ p2307) ∨ (¬ p2751) ∨ (¬ p3568) ∨ (¬ p4195) ∨ (¬ p4759) ∨ (¬ p5016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10317 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41449 (p2027 p2088 p3097 p3743 p4114 p4347 p4405 : Prop)
    (h40810 : (¬ p2027))
    (h10320 : p2027 ∨ (¬ p2088) ∨ (¬ p3097) ∨ (¬ p3743) ∨ (¬ p4114) ∨ (¬ p4347) ∨ (¬ p4405))
    : (¬ p2088) ∨ (¬ p3097) ∨ (¬ p3743) ∨ (¬ p4114) ∨ (¬ p4347) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4114 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10320 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41451 (p2027 p2249 p2657 p2922 p3742 p4281 : Prop)
    (h40810 : (¬ p2027))
    (h10323 : p2027 ∨ (¬ p2249) ∨ (¬ p2657) ∨ (¬ p2922) ∨ (¬ p3742) ∨ (¬ p4281))
    : (¬ p2249) ∨ (¬ p2657) ∨ (¬ p2922) ∨ (¬ p3742) ∨ (¬ p4281) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2249 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10323 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41454 (p2027 p2274 p2331 p3414 p3740 p3921 p4564 : Prop)
    (h40810 : (¬ p2027))
    (h10326 : p2027 ∨ (¬ p2274) ∨ (¬ p2331) ∨ (¬ p3414) ∨ (¬ p3740) ∨ (¬ p3921) ∨ (¬ p4564))
    : (¬ p2274) ∨ (¬ p2331) ∨ (¬ p3414) ∨ (¬ p3740) ∨ (¬ p3921) ∨ (¬ p4564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10326 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41455 (p2027 p2246 p2284 p2946 p2996 p3699 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h10327 : p2027 ∨ (¬ p2246) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p2996) ∨ (¬ p3699) ∨ (¬ p4555))
    : (¬ p2246) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p2996) ∨ (¬ p3699) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3699 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10327 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41457 (p2027 p2972 p4034 p4037 p4110 p4564 p5045 : Prop)
    (h40810 : (¬ p2027))
    (h10329 : p2027 ∨ (¬ p2972) ∨ (¬ p4034) ∨ (¬ p4037) ∨ (¬ p4110) ∨ (¬ p4564) ∨ (¬ p5045))
    : (¬ p2972) ∨ (¬ p4034) ∨ (¬ p4037) ∨ (¬ p4110) ∨ (¬ p4564) ∨ (¬ p5045) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4034 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10329 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41458 (p2027 p3599 p3688 p4037 p4846 p5269 : Prop)
    (h40810 : (¬ p2027))
    (h10330 : p2027 ∨ (¬ p3599) ∨ (¬ p3688) ∨ (¬ p4037) ∨ (¬ p4846) ∨ (¬ p5269))
    : (¬ p3599) ∨ (¬ p3688) ∨ (¬ p4037) ∨ (¬ p4846) ∨ (¬ p5269) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3599 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4846 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5269 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10330 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41459 (p2027 p2563 p2891 p3556 p4173 p4533 : Prop)
    (h40810 : (¬ p2027))
    (h10331 : p2027 ∨ (¬ p2563) ∨ (¬ p2891) ∨ (¬ p3556) ∨ (¬ p4173) ∨ (¬ p4533))
    : (¬ p2563) ∨ (¬ p2891) ∨ (¬ p3556) ∨ (¬ p4173) ∨ (¬ p4533) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10331 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41460 (p2027 p2982 p3947 p4135 p4235 p4280 : Prop)
    (h40810 : (¬ p2027))
    (h10332 : p2027 ∨ (¬ p2982) ∨ (¬ p3947) ∨ (¬ p4135) ∨ (¬ p4235) ∨ (¬ p4280))
    : (¬ p2982) ∨ (¬ p3947) ∨ (¬ p4135) ∨ (¬ p4235) ∨ (¬ p4280) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4135 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4280 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10332 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41461 (p2027 p2685 p3040 p3527 p3877 p4548 : Prop)
    (h40810 : (¬ p2027))
    (h10333 : p2027 ∨ (¬ p2685) ∨ (¬ p3040) ∨ (¬ p3527) ∨ (¬ p3877) ∨ (¬ p4548))
    : (¬ p2685) ∨ (¬ p3040) ∨ (¬ p3527) ∨ (¬ p3877) ∨ (¬ p4548) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2685 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3040 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10333 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41462 (p2027 p2751 p3038 p3527 p3551 p3572 p4155 : Prop)
    (h40810 : (¬ p2027))
    (h10334 : p2027 ∨ (¬ p2751) ∨ (¬ p3038) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p3572) ∨ (¬ p4155))
    : (¬ p2751) ∨ (¬ p3038) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p3572) ∨ (¬ p4155) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2751 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3038 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10334 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41464 (p2027 p2685 p3040 p3516 p3543 p4035 p4656 : Prop)
    (h40810 : (¬ p2027))
    (h10336 : p2027 ∨ (¬ p2685) ∨ (¬ p3040) ∨ (¬ p3516) ∨ (¬ p3543) ∨ (¬ p4035) ∨ (¬ p4656))
    : (¬ p2685) ∨ (¬ p3040) ∨ (¬ p3516) ∨ (¬ p3543) ∨ (¬ p4035) ∨ (¬ p4656) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2685 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3040 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3543 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4035 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10336 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41465 (p2027 p2528 p3324 p3875 p3920 p4347 p4973 : Prop)
    (h40810 : (¬ p2027))
    (h10337 : p2027 ∨ (¬ p2528) ∨ (¬ p3324) ∨ (¬ p3875) ∨ (¬ p3920) ∨ (¬ p4347) ∨ (¬ p4973))
    : (¬ p2528) ∨ (¬ p3324) ∨ (¬ p3875) ∨ (¬ p3920) ∨ (¬ p4347) ∨ (¬ p4973) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3920 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10337 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41466 (p2027 p2156 p3737 p4032 p4033 p5253 : Prop)
    (h40810 : (¬ p2027))
    (h10338 : p2027 ∨ (¬ p2156) ∨ (¬ p3737) ∨ (¬ p4032) ∨ (¬ p4033) ∨ (¬ p5253))
    : (¬ p2156) ∨ (¬ p3737) ∨ (¬ p4032) ∨ (¬ p4033) ∨ (¬ p5253) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4033 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10338 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41467 (p2027 p2284 p2528 p3661 p3875 p4001 p4118 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h10339 : p2027 ∨ (¬ p2284) ∨ (¬ p2528) ∨ (¬ p3661) ∨ (¬ p3875) ∨ (¬ p4001) ∨ (¬ p4118) ∨ (¬ p4555))
    : (¬ p2284) ∨ (¬ p2528) ∨ (¬ p3661) ∨ (¬ p3875) ∨ (¬ p4001) ∨ (¬ p4118) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h10339 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41469 (p2027 p2528 p3266 p3322 p4191 p4384 : Prop)
    (h40810 : (¬ p2027))
    (h10341 : p2027 ∨ (¬ p2528) ∨ (¬ p3266) ∨ (¬ p3322) ∨ (¬ p4191) ∨ (¬ p4384))
    : (¬ p2528) ∨ (¬ p3266) ∨ (¬ p3322) ∨ (¬ p4191) ∨ (¬ p4384) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4384 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10341 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41470 (p2027 p2528 p2668 p3693 p4037 p4134 p4171 : Prop)
    (h40810 : (¬ p2027))
    (h10342 : p2027 ∨ (¬ p2528) ∨ (¬ p2668) ∨ (¬ p3693) ∨ (¬ p4037) ∨ (¬ p4134) ∨ (¬ p4171))
    : (¬ p2528) ∨ (¬ p2668) ∨ (¬ p3693) ∨ (¬ p4037) ∨ (¬ p4134) ∨ (¬ p4171) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10342 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41472 (p2027 p2749 p2952 p2992 p3361 p3688 p4842 : Prop)
    (h40810 : (¬ p2027))
    (h10344 : p2027 ∨ (¬ p2749) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3361) ∨ (¬ p3688) ∨ (¬ p4842))
    : (¬ p2749) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3361) ∨ (¬ p3688) ∨ (¬ p4842) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2749 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10344 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41474 (p2027 p2331 p2952 p3986 p4320 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h10346 : p2027 ∨ (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3986) ∨ (¬ p4320) ∨ (¬ p4555))
    : (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3986) ∨ (¬ p4320) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10346 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41475 (p2027 p2383 p3073 p3946 p4171 p4370 p4384 : Prop)
    (h40810 : (¬ p2027))
    (h10347 : p2027 ∨ (¬ p2383) ∨ (¬ p3073) ∨ (¬ p3946) ∨ (¬ p4171) ∨ (¬ p4370) ∨ (¬ p4384))
    : (¬ p2383) ∨ (¬ p3073) ∨ (¬ p3946) ∨ (¬ p4171) ∨ (¬ p4370) ∨ (¬ p4384) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4384 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10347 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41476 (p2027 p2264 p2651 p3551 p4650 p4849 : Prop)
    (h40810 : (¬ p2027))
    (h10348 : p2027 ∨ (¬ p2264) ∨ (¬ p2651) ∨ (¬ p3551) ∨ (¬ p4650) ∨ (¬ p4849))
    : (¬ p2264) ∨ (¬ p2651) ∨ (¬ p3551) ∨ (¬ p4650) ∨ (¬ p4849) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4849 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10348 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41477 (p2027 p2499 p2922 p3568 p4710 p4973 : Prop)
    (h40810 : (¬ p2027))
    (h10349 : p2027 ∨ (¬ p2499) ∨ (¬ p2922) ∨ (¬ p3568) ∨ (¬ p4710) ∨ (¬ p4973))
    : (¬ p2499) ∨ (¬ p2922) ∨ (¬ p3568) ∨ (¬ p4710) ∨ (¬ p4973) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2499 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10349 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41478 (p2027 p2299 p2911 p3568 p3920 p4973 : Prop)
    (h40810 : (¬ p2027))
    (h10350 : p2027 ∨ (¬ p2299) ∨ (¬ p2911) ∨ (¬ p3568) ∨ (¬ p3920) ∨ (¬ p4973))
    : (¬ p2299) ∨ (¬ p2911) ∨ (¬ p3568) ∨ (¬ p3920) ∨ (¬ p4973) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3920 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10350 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41484 (p2027 p2230 p2528 p2577 p3857 p4197 p4608 : Prop)
    (h40810 : (¬ p2027))
    (h10356 : p2027 ∨ (¬ p2230) ∨ (¬ p2528) ∨ (¬ p2577) ∨ (¬ p3857) ∨ (¬ p4197) ∨ (¬ p4608))
    : (¬ p2230) ∨ (¬ p2528) ∨ (¬ p2577) ∨ (¬ p3857) ∨ (¬ p4197) ∨ (¬ p4608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10356 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41485 (p2027 p2311 p2383 p2396 p3821 p4405 : Prop)
    (h40810 : (¬ p2027))
    (h10357 : p2027 ∨ (¬ p2311) ∨ (¬ p2383) ∨ (¬ p2396) ∨ (¬ p3821) ∨ (¬ p4405))
    : (¬ p2311) ∨ (¬ p2383) ∨ (¬ p2396) ∨ (¬ p3821) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2311 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10357 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41486 (p2027 p2383 p3743 p3744 p3979 p4171 p5122 : Prop)
    (h40810 : (¬ p2027))
    (h10358 : p2027 ∨ (¬ p2383) ∨ (¬ p3743) ∨ (¬ p3744) ∨ (¬ p3979) ∨ (¬ p4171) ∨ (¬ p5122))
    : (¬ p2383) ∨ (¬ p3743) ∨ (¬ p3744) ∨ (¬ p3979) ∨ (¬ p4171) ∨ (¬ p5122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10358 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41489 (p2027 p2911 p3556 p3570 p3741 p4533 : Prop)
    (h40810 : (¬ p2027))
    (h10361 : p2027 ∨ (¬ p2911) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3741) ∨ (¬ p4533))
    : (¬ p2911) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3741) ∨ (¬ p4533) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10361 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41490 (p2027 p2298 p2641 p2996 p4228 p5477 : Prop)
    (h40810 : (¬ p2027))
    (h10362 : p2027 ∨ (¬ p2298) ∨ (¬ p2641) ∨ (¬ p2996) ∨ (¬ p4228) ∨ (¬ p5477))
    : (¬ p2298) ∨ (¬ p2641) ∨ (¬ p2996) ∨ (¬ p4228) ∨ (¬ p5477) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2298 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4228 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10362 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41491 (p2027 p2807 p2911 p3172 p4327 p4548 : Prop)
    (h40810 : (¬ p2027))
    (h10363 : p2027 ∨ (¬ p2807) ∨ (¬ p2911) ∨ (¬ p3172) ∨ (¬ p4327) ∨ (¬ p4548))
    : (¬ p2807) ∨ (¬ p2911) ∨ (¬ p3172) ∨ (¬ p4327) ∨ (¬ p4548) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2807 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4327 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10363 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41492 (p2027 p3319 p3662 p4037 p4566 p4759 : Prop)
    (h40810 : (¬ p2027))
    (h10364 : p2027 ∨ (¬ p3319) ∨ (¬ p3662) ∨ (¬ p4037) ∨ (¬ p4566) ∨ (¬ p4759))
    : (¬ p3319) ∨ (¬ p3662) ∨ (¬ p4037) ∨ (¬ p4566) ∨ (¬ p4759) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4566 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10364 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41493 (p2027 p2459 p2499 p2881 p3051 p3452 p4137 p4521 p4604 : Prop)
    (h40810 : (¬ p2027))
    (h10365 : p2027 ∨ (¬ p2459) ∨ (¬ p2499) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3452) ∨ (¬ p4137) ∨ (¬ p4521) ∨ (¬ p4604))
    : (¬ p2459) ∨ (¬ p2499) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3452) ∨ (¬ p4137) ∨ (¬ p4521) ∨ (¬ p4604) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h10365 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step41494 (p2027 p2656 p2727 p3389 p3662 p3879 p4646 : Prop)
    (h40810 : (¬ p2027))
    (h10366 : p2027 ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p3389) ∨ (¬ p3662) ∨ (¬ p3879) ∨ (¬ p4646))
    : (¬ p2656) ∨ (¬ p2727) ∨ (¬ p3389) ∨ (¬ p3662) ∨ (¬ p3879) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2656 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10366 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41495 (p2027 p2341 p2427 p3553 p3691 p4386 p4702 : Prop)
    (h40810 : (¬ p2027))
    (h10367 : p2027 ∨ (¬ p2341) ∨ (¬ p2427) ∨ (¬ p3553) ∨ (¬ p3691) ∨ (¬ p4386) ∨ (¬ p4702))
    : (¬ p2341) ∨ (¬ p2427) ∨ (¬ p3553) ∨ (¬ p3691) ∨ (¬ p4386) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10367 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41496 (p2027 p3570 p3875 p4149 p4647 p5558 : Prop)
    (h40810 : (¬ p2027))
    (h10368 : p2027 ∨ (¬ p3570) ∨ (¬ p3875) ∨ (¬ p4149) ∨ (¬ p4647) ∨ (¬ p5558))
    : (¬ p3570) ∨ (¬ p3875) ∨ (¬ p4149) ∨ (¬ p4647) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3570 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4149 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10368 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41497 (p2027 p2911 p3551 p3741 p4283 p4320 p4702 : Prop)
    (h40810 : (¬ p2027))
    (h10369 : p2027 ∨ (¬ p2911) ∨ (¬ p3551) ∨ (¬ p3741) ∨ (¬ p4283) ∨ (¬ p4320) ∨ (¬ p4702))
    : (¬ p2911) ∨ (¬ p3551) ∨ (¬ p3741) ∨ (¬ p4283) ∨ (¬ p4320) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10369 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41499 (p2027 p3256 p3692 p3988 p4237 p4320 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h10371 : p2027 ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4237) ∨ (¬ p4320) ∨ (¬ p4555))
    : (¬ p3256) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4237) ∨ (¬ p4320) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4237 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10371 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41500 (p2027 p2274 p2563 p3568 p4153 p4702 : Prop)
    (h40810 : (¬ p2027))
    (h10372 : p2027 ∨ (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3568) ∨ (¬ p4153) ∨ (¬ p4702))
    : (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3568) ∨ (¬ p4153) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10372 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41504 (p2027 p2156 p2427 p3556 p3745 p4153 p4702 : Prop)
    (h40810 : (¬ p2027))
    (h10377 : p2027 ∨ (¬ p2156) ∨ (¬ p2427) ∨ (¬ p3556) ∨ (¬ p3745) ∨ (¬ p4153) ∨ (¬ p4702))
    : (¬ p2156) ∨ (¬ p2427) ∨ (¬ p3556) ∨ (¬ p3745) ∨ (¬ p4153) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10377 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41506 (p2027 p2192 p2662 p2996 p3646 p3904 p4365 p4650 : Prop)
    (h40810 : (¬ p2027))
    (h10379 : p2027 ∨ (¬ p2192) ∨ (¬ p2662) ∨ (¬ p2996) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4365) ∨ (¬ p4650))
    : (¬ p2192) ∨ (¬ p2662) ∨ (¬ p2996) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4365) ∨ (¬ p4650) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h10379 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41508 (p2027 p3888 p3956 p4771 p5584 p5600 : Prop)
    (h40810 : (¬ p2027))
    (h10381 : p2027 ∨ (¬ p3888) ∨ (¬ p3956) ∨ (¬ p4771) ∨ (¬ p5584) ∨ (¬ p5600))
    : (¬ p3888) ∨ (¬ p3956) ∨ (¬ p4771) ∨ (¬ p5584) ∨ (¬ p5600) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3888 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4771 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10381 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41510 (p2027 p2427 p3222 p3486 p4202 p4953 : Prop)
    (h40810 : (¬ p2027))
    (h10383 : p2027 ∨ (¬ p2427) ∨ (¬ p3222) ∨ (¬ p3486) ∨ (¬ p4202) ∨ (¬ p4953))
    : (¬ p2427) ∨ (¬ p3222) ∨ (¬ p3486) ∨ (¬ p4202) ∨ (¬ p4953) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10383 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41511 (p2027 p2088 p2475 p2518 p3878 p4118 p4814 : Prop)
    (h40810 : (¬ p2027))
    (h10385 : p2027 ∨ (¬ p2088) ∨ (¬ p2475) ∨ (¬ p2518) ∨ (¬ p3878) ∨ (¬ p4118) ∨ (¬ p4814))
    : (¬ p2088) ∨ (¬ p2475) ∨ (¬ p2518) ∨ (¬ p3878) ∨ (¬ p4118) ∨ (¬ p4814) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3878 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10385 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41512 (p2027 p3073 p3266 p4322 p4335 p4498 : Prop)
    (h40810 : (¬ p2027))
    (h10386 : p2027 ∨ (¬ p3073) ∨ (¬ p3266) ∨ (¬ p4322) ∨ (¬ p4335) ∨ (¬ p4498))
    : (¬ p3073) ∨ (¬ p3266) ∨ (¬ p4322) ∨ (¬ p4335) ∨ (¬ p4498) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4335 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4498 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10386 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41513 (p2027 p2166 p3146 p3661 p4118 p4960 : Prop)
    (h40810 : (¬ p2027))
    (h10387 : p2027 ∨ (¬ p2166) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p4960))
    : (¬ p2166) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p4960) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10387 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41514 (p2027 p2274 p2284 p4033 p4208 p4620 : Prop)
    (h40810 : (¬ p2027))
    (h10388 : p2027 ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p4033) ∨ (¬ p4208) ∨ (¬ p4620))
    : (¬ p2274) ∨ (¬ p2284) ∨ (¬ p4033) ∨ (¬ p4208) ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4033 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10388 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41518 (p2027 p2352 p2493 p3324 p4194 p4814 : Prop)
    (h40810 : (¬ p2027))
    (h10392 : p2027 ∨ (¬ p2352) ∨ (¬ p2493) ∨ (¬ p3324) ∨ (¬ p4194) ∨ (¬ p4814))
    : (¬ p2352) ∨ (¬ p2493) ∨ (¬ p3324) ∨ (¬ p4194) ∨ (¬ p4814) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10392 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41519 (p2027 p2493 p2598 p2780 p4342 p5217 : Prop)
    (h40810 : (¬ p2027))
    (h10393 : p2027 ∨ (¬ p2493) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (¬ p4342) ∨ (¬ p5217))
    : (¬ p2493) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (¬ p4342) ∨ (¬ p5217) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4342 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5217 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10393 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41520 (p2027 p2406 p2563 p3646 p3904 p5191 : Prop)
    (h40810 : (¬ p2027))
    (h10394 : p2027 ∨ (¬ p2406) ∨ (¬ p2563) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p5191))
    : (¬ p2406) ∨ (¬ p2563) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p5191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10394 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41522 (p2027 p2598 p2922 p3425 p4106 p5217 : Prop)
    (h40810 : (¬ p2027))
    (h10413 : p2027 ∨ (¬ p2598) ∨ (¬ p2922) ∨ (¬ p3425) ∨ (¬ p4106) ∨ (¬ p5217))
    : (¬ p2598) ∨ (¬ p2922) ∨ (¬ p3425) ∨ (¬ p4106) ∨ (¬ p5217) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4106 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5217 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10413 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41524 (p2027 p2475 p2518 p2630 p3177 p3877 p4814 : Prop)
    (h40810 : (¬ p2027))
    (h10415 : p2027 ∨ (¬ p2475) ∨ (¬ p2518) ∨ (¬ p2630) ∨ (¬ p3177) ∨ (¬ p3877) ∨ (¬ p4814))
    : (¬ p2475) ∨ (¬ p2518) ∨ (¬ p2630) ∨ (¬ p3177) ∨ (¬ p3877) ∨ (¬ p4814) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2475 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10415 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41526 (p2027 p2341 p2922 p3575 p3659 p3686 p5217 : Prop)
    (h40810 : (¬ p2027))
    (h10417 : p2027 ∨ (¬ p2341) ∨ (¬ p2922) ∨ (¬ p3575) ∨ (¬ p3659) ∨ (¬ p3686) ∨ (¬ p5217))
    : (¬ p2341) ∨ (¬ p2922) ∨ (¬ p3575) ∨ (¬ p3659) ∨ (¬ p3686) ∨ (¬ p5217) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3686 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5217 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10417 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41528 (p2027 p2441 p2589 p3093 p3309 p3921 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h10419 : p2027 ∨ (¬ p2441) ∨ (¬ p2589) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3921) ∨ (¬ p5193))
    : (¬ p2441) ∨ (¬ p2589) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3921) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2441 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10419 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41530 (p2027 p2274 p2313 p3063 p3204 p3744 p4601 : Prop)
    (h40810 : (¬ p2027))
    (h10421 : p2027 ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p3063) ∨ (¬ p3204) ∨ (¬ p3744) ∨ (¬ p4601))
    : (¬ p2274) ∨ (¬ p2313) ∨ (¬ p3063) ∨ (¬ p3204) ∨ (¬ p3744) ∨ (¬ p4601) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4601 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10421 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41534 (p2027 p2727 p2850 p2957 p3662 p4109 p4753 : Prop)
    (h40810 : (¬ p2027))
    (h10425 : p2027 ∨ (¬ p2727) ∨ (¬ p2850) ∨ (¬ p2957) ∨ (¬ p3662) ∨ (¬ p4109) ∨ (¬ p4753))
    : (¬ p2727) ∨ (¬ p2850) ∨ (¬ p2957) ∨ (¬ p3662) ∨ (¬ p4109) ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10425 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41536 (p2027 p2589 p3097 p3399 p3527 p3553 p4110 p4570 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h10427 : p2027 ∨ (¬ p2589) ∨ (¬ p3097) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3553) ∨ (¬ p4110) ∨ (¬ p4570) ∨ (¬ p5193))
    : (¬ p2589) ∨ (¬ p3097) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3553) ∨ (¬ p4110) ∨ (¬ p4570) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h10427 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step41538 (p2027 p3246 p3947 p4067 p4228 p4275 p5477 : Prop)
    (h40810 : (¬ p2027))
    (h10446 : p2027 ∨ (¬ p3246) ∨ (¬ p3947) ∨ (¬ p4067) ∨ (¬ p4228) ∨ (¬ p4275) ∨ (¬ p5477))
    : (¬ p3246) ∨ (¬ p3947) ∨ (¬ p4067) ∨ (¬ p4228) ∨ (¬ p4275) ∨ (¬ p5477) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4228 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10446 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41542 (p2027 p2241 p2589 p3027 p3744 p3872 p3931 p4235 p4396 p4830 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h10450 : p2027 ∨ (¬ p2241) ∨ (¬ p2589) ∨ (¬ p3027) ∨ (¬ p3744) ∨ (¬ p3872) ∨ (¬ p3931) ∨ (¬ p4235) ∨ (¬ p4396) ∨ (¬ p4830) ∨ (¬ p5193))
    : (¬ p2241) ∨ (¬ p2589) ∨ (¬ p3027) ∨ (¬ p3744) ∨ (¬ p3872) ∨ (¬ p3931) ∨ (¬ p4235) ∨ (¬ p4396) ∨ (¬ p4830) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h10450 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step41546 (p2027 p2761 p2952 p3361 p3425 p3619 p3952 p4393 p4778 p5233 p5254 : Prop)
    (h40810 : (¬ p2027))
    (h10455 : p2027 ∨ (¬ p2761) ∨ (¬ p2952) ∨ (¬ p3361) ∨ (¬ p3425) ∨ (¬ p3619) ∨ (¬ p3952) ∨ (¬ p4393) ∨ (¬ p4778) ∨ (¬ p5233) ∨ (¬ p5254))
    : (¬ p2761) ∨ (¬ p2952) ∨ (¬ p3361) ∨ (¬ p3425) ∨ (¬ p3619) ∨ (¬ p3952) ∨ (¬ p4393) ∨ (¬ p4778) ∨ (¬ p5233) ∨ (¬ p5254) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5233 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h10455 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step41551 (p2027 p2542 p2589 p3399 p3527 p3659 p3742 p5083 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h10460 : p2027 ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3659) ∨ (¬ p3742) ∨ (¬ p5083) ∨ (¬ p5193))
    : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3659) ∨ (¬ p3742) ∨ (¬ p5083) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h10460 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step41555 (p2027 p2717 p3367 p3548 p4400 p4752 p4781 : Prop)
    (h40810 : (¬ p2027))
    (h10464 : p2027 ∨ (¬ p2717) ∨ (¬ p3367) ∨ (¬ p3548) ∨ (¬ p4400) ∨ (¬ p4752) ∨ (¬ p4781))
    : (¬ p2717) ∨ (¬ p3367) ∨ (¬ p3548) ∨ (¬ p4400) ∨ (¬ p4752) ∨ (¬ p4781) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4400 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10464 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41556 (p2027 p2741 p2811 p3166 p3367 p4360 p4752 : Prop)
    (h40810 : (¬ p2027))
    (h10465 : p2027 ∨ (¬ p2741) ∨ (¬ p2811) ∨ (¬ p3166) ∨ (¬ p3367) ∨ (¬ p4360) ∨ (¬ p4752))
    : (¬ p2741) ∨ (¬ p2811) ∨ (¬ p3166) ∨ (¬ p3367) ∨ (¬ p4360) ∨ (¬ p4752) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2741 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10465 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41561 (p2027 p2166 p2946 p3172 p4312 p4960 : Prop)
    (h40810 : (¬ p2027))
    (h10470 : p2027 ∨ (¬ p2166) ∨ (¬ p2946) ∨ (¬ p3172) ∨ (¬ p4312) ∨ (¬ p4960))
    : (¬ p2166) ∨ (¬ p2946) ∨ (¬ p3172) ∨ (¬ p4312) ∨ (¬ p4960) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10470 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41567 (p2027 p2499 p2761 p3051 p3246 p3452 p4521 p5254 p5514 : Prop)
    (h40810 : (¬ p2027))
    (h10476 : p2027 ∨ (¬ p2499) ∨ (¬ p2761) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3452) ∨ (¬ p4521) ∨ (¬ p5254) ∨ (¬ p5514))
    : (¬ p2499) ∨ (¬ p2761) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3452) ∨ (¬ p4521) ∨ (¬ p5254) ∨ (¬ p5514) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2499 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h10476 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step41568 (p2027 p2954 p3189 p3662 p4120 p4311 : Prop)
    (h40810 : (¬ p2027))
    (h10477 : p2027 ∨ (¬ p2954) ∨ (¬ p3189) ∨ (¬ p3662) ∨ (¬ p4120) ∨ (¬ p4311))
    : (¬ p2954) ∨ (¬ p3189) ∨ (¬ p3662) ∨ (¬ p4120) ∨ (¬ p4311) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2954 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10477 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41571 (p2027 p2641 p2954 p3646 p3662 p3986 : Prop)
    (h40810 : (¬ p2027))
    (h10481 : p2027 ∨ (¬ p2641) ∨ (¬ p2954) ∨ (¬ p3646) ∨ (¬ p3662) ∨ (¬ p3986))
    : (¬ p2641) ∨ (¬ p2954) ∨ (¬ p3646) ∨ (¬ p3662) ∨ (¬ p3986) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10481 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41572 (p2027 p2542 p2563 p2659 p3646 p3904 : Prop)
    (h40810 : (¬ p2027))
    (h10482 : p2027 ∨ (¬ p2542) ∨ (¬ p2563) ∨ (¬ p2659) ∨ (¬ p3646) ∨ (¬ p3904))
    : (¬ p2542) ∨ (¬ p2563) ∨ (¬ p2659) ∨ (¬ p3646) ∨ (¬ p3904) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10482 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41574 (p2027 p2659 p2685 p2810 p3540 p3579 : Prop)
    (h40810 : (¬ p2027))
    (h10484 : p2027 ∨ (¬ p2659) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p3540) ∨ (¬ p3579))
    : (¬ p2659) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p3540) ∨ (¬ p3579) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2659 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10484 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41576 (p2027 p2499 p2588 p2662 p3083 p3519 p4157 p4405 : Prop)
    (h40810 : (¬ p2027))
    (h10486 : p2027 ∨ (¬ p2499) ∨ (¬ p2588) ∨ (¬ p2662) ∨ (¬ p3083) ∨ (¬ p3519) ∨ (¬ p4157) ∨ (¬ p4405))
    : (¬ p2499) ∨ (¬ p2588) ∨ (¬ p2662) ∨ (¬ p3083) ∨ (¬ p3519) ∨ (¬ p4157) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2499 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h10486 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41578 (p2027 p2166 p2589 p3880 p3948 p5191 : Prop)
    (h40810 : (¬ p2027))
    (h10488 : p2027 ∨ (¬ p2166) ∨ (¬ p2589) ∨ (¬ p3880) ∨ (¬ p3948) ∨ (¬ p5191))
    : (¬ p2166) ∨ (¬ p2589) ∨ (¬ p3880) ∨ (¬ p3948) ∨ (¬ p5191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10488 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41579 (p2027 p2252 p2440 p2657 p2750 p3399 p3527 p3880 p3954 p4905 : Prop)
    (h40810 : (¬ p2027))
    (h10489 : p2027 ∨ (¬ p2252) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3880) ∨ (¬ p3954) ∨ (¬ p4905))
    : (¬ p2252) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3880) ∨ (¬ p3954) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h10489 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step41580 (p2027 p2241 p2748 p3588 p3954 p4778 : Prop)
    (h40810 : (¬ p2027))
    (h10490 : p2027 ∨ (¬ p2241) ∨ (¬ p2748) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p4778))
    : (¬ p2241) ∨ (¬ p2748) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p4778) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10490 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41581 (p2027 p2252 p2750 p2963 p3324 p3399 p3631 p3950 p3954 p4347 : Prop)
    (h40810 : (¬ p2027))
    (h10491 : p2027 ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3950) ∨ (¬ p3954) ∨ (¬ p4347))
    : (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3950) ∨ (¬ p3954) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h10491 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step41582 (p2027 p2247 p2751 p3449 p3877 p4288 : Prop)
    (h40810 : (¬ p2027))
    (h10492 : p2027 ∨ (¬ p2247) ∨ (¬ p2751) ∨ (¬ p3449) ∨ (¬ p3877) ∨ (¬ p4288))
    : (¬ p2247) ∨ (¬ p2751) ∨ (¬ p3449) ∨ (¬ p3877) ∨ (¬ p4288) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4288 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10492 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41583 (p2027 p3954 p3998 p5242 p5317 p5693 : Prop)
    (h40810 : (¬ p2027))
    (h10494 : p2027 ∨ (¬ p3954) ∨ (¬ p3998) ∨ (¬ p5242) ∨ (¬ p5317) ∨ (¬ p5693))
    : (¬ p3954) ∨ (¬ p3998) ∨ (¬ p5242) ∨ (¬ p5317) ∨ (¬ p5693) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3954 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5317 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10494 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41584 (p2027 p2192 p3554 p4129 p4442 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h10495 : p2027 ∨ (¬ p2192) ∨ (¬ p3554) ∨ (¬ p4129) ∨ (¬ p4442) ∨ (¬ p4555))
    : (¬ p2192) ∨ (¬ p3554) ∨ (¬ p4129) ∨ (¬ p4442) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3554 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4129 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4442 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10495 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41585 (p2027 p2352 p2497 p3016 p3923 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h10496 : p2027 ∨ (¬ p2352) ∨ (¬ p2497) ∨ (¬ p3016) ∨ (¬ p3923) ∨ (¬ p4811))
    : (¬ p2352) ∨ (¬ p2497) ∨ (¬ p3016) ∨ (¬ p3923) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10496 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41586 (p2027 p2088 p3954 p4261 p5242 p5317 : Prop)
    (h40810 : (¬ p2027))
    (h10497 : p2027 ∨ (¬ p2088) ∨ (¬ p3954) ∨ (¬ p4261) ∨ (¬ p5242) ∨ (¬ p5317))
    : (¬ p2088) ∨ (¬ p3954) ∨ (¬ p4261) ∨ (¬ p5242) ∨ (¬ p5317) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5317 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10497 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41587 (p2027 p2252 p2579 p2655 p2750 p3016 p3399 p3527 p3954 p4256 p4438 : Prop)
    (h40810 : (¬ p2027))
    (h10498 : p2027 ∨ (¬ p2252) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p3016) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3954) ∨ (¬ p4256) ∨ (¬ p4438))
    : (¬ p2252) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p3016) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3954) ∨ (¬ p4256) ∨ (¬ p4438) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h10498 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step41588 (p2027 p2156 p2437 p3575 p4173 p4202 p4811 p4984 : Prop)
    (h40810 : (¬ p2027))
    (h10499 : p2027 ∨ (¬ p2156) ∨ (¬ p2437) ∨ (¬ p3575) ∨ (¬ p4173) ∨ (¬ p4202) ∨ (¬ p4811) ∨ (¬ p4984))
    : (¬ p2156) ∨ (¬ p2437) ∨ (¬ p3575) ∨ (¬ p4173) ∨ (¬ p4202) ∨ (¬ p4811) ∨ (¬ p4984) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h10499 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41590 (p2027 p2437 p2927 p3379 p4366 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h10501 : p2027 ∨ (¬ p2437) ∨ (¬ p2927) ∨ (¬ p3379) ∨ (¬ p4366) ∨ (¬ p4811))
    : (¬ p2437) ∨ (¬ p2927) ∨ (¬ p3379) ∨ (¬ p4366) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2927 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10501 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41591 (p2027 p2352 p3146 p4134 p4137 p4171 : Prop)
    (h40810 : (¬ p2027))
    (h10502 : p2027 ∨ (¬ p2352) ∨ (¬ p3146) ∨ (¬ p4134) ∨ (¬ p4137) ∨ (¬ p4171))
    : (¬ p2352) ∨ (¬ p3146) ∨ (¬ p4134) ∨ (¬ p4137) ∨ (¬ p4171) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10502 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41593 (p2027 p2252 p2750 p2952 p3399 p3631 p3744 p3952 p3954 p4625 : Prop)
    (h40810 : (¬ p2027))
    (h10504 : p2027 ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p3954) ∨ (¬ p4625))
    : (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p3954) ∨ (¬ p4625) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h10504 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step41594 (p2027 p2274 p2588 p3564 p4037 p4564 : Prop)
    (h40810 : (¬ p2027))
    (h10505 : p2027 ∨ (¬ p2274) ∨ (¬ p2588) ∨ (¬ p3564) ∨ (¬ p4037) ∨ (¬ p4564))
    : (¬ p2274) ∨ (¬ p2588) ∨ (¬ p3564) ∨ (¬ p4037) ∨ (¬ p4564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10505 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41595 (p2027 p2470 p2579 p3324 p4157 p4973 : Prop)
    (h40810 : (¬ p2027))
    (h10507 : p2027 ∨ (¬ p2470) ∨ (¬ p2579) ∨ (¬ p3324) ∨ (¬ p4157) ∨ (¬ p4973))
    : (¬ p2470) ∨ (¬ p2579) ∨ (¬ p3324) ∨ (¬ p4157) ∨ (¬ p4973) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10507 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41596 (p2027 p3461 p3564 p3922 p4321 p4430 p4973 : Prop)
    (h40810 : (¬ p2027))
    (h10508 : p2027 ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p3922) ∨ (¬ p4321) ∨ (¬ p4430) ∨ (¬ p4973))
    : (¬ p3461) ∨ (¬ p3564) ∨ (¬ p3922) ∨ (¬ p4321) ∨ (¬ p4430) ∨ (¬ p4973) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4321 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4430 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10508 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41597 (p2027 p2717 p2933 p3540 p3548 p4727 p5085 : Prop)
    (h40810 : (¬ p2027))
    (h10509 : p2027 ∨ (¬ p2717) ∨ (¬ p2933) ∨ (¬ p3540) ∨ (¬ p3548) ∨ (¬ p4727) ∨ (¬ p5085))
    : (¬ p2717) ∨ (¬ p2933) ∨ (¬ p3540) ∨ (¬ p3548) ∨ (¬ p4727) ∨ (¬ p5085) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2933 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5085 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10509 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41598 (p2027 p2922 p3238 p3575 p4283 p4320 p4702 : Prop)
    (h40810 : (¬ p2027))
    (h10510 : p2027 ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3575) ∨ (¬ p4283) ∨ (¬ p4320) ∨ (¬ p4702))
    : (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3575) ∨ (¬ p4283) ∨ (¬ p4320) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10510 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41600 (p2027 p2934 p3238 p3527 p3551 p4279 p4646 : Prop)
    (h40810 : (¬ p2027))
    (h10512 : p2027 ∨ (¬ p2934) ∨ (¬ p3238) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p4279) ∨ (¬ p4646))
    : (¬ p2934) ∨ (¬ p3238) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p4279) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2934 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4279 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10512 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41602 (p2027 p3246 p3346 p3389 p4277 p4636 : Prop)
    (h40810 : (¬ p2027))
    (h10514 : p2027 ∨ (¬ p3246) ∨ (¬ p3346) ∨ (¬ p3389) ∨ (¬ p4277) ∨ (¬ p4636))
    : (¬ p3246) ∨ (¬ p3346) ∨ (¬ p3389) ∨ (¬ p4277) ∨ (¬ p4636) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4636 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10514 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41604 (p2027 p2427 p3568 p4110 p4140 p4564 : Prop)
    (h40810 : (¬ p2027))
    (h10516 : p2027 ∨ (¬ p2427) ∨ (¬ p3568) ∨ (¬ p4110) ∨ (¬ p4140) ∨ (¬ p4564))
    : (¬ p2427) ∨ (¬ p3568) ∨ (¬ p4110) ∨ (¬ p4140) ∨ (¬ p4564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10516 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41605 (p2027 p2470 p2577 p3564 p3946 p4598 : Prop)
    (h40810 : (¬ p2027))
    (h10517 : p2027 ∨ (¬ p2470) ∨ (¬ p2577) ∨ (¬ p3564) ∨ (¬ p3946) ∨ (¬ p4598))
    : (¬ p2470) ∨ (¬ p2577) ∨ (¬ p3564) ∨ (¬ p3946) ∨ (¬ p4598) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10517 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41606 (p2027 p2187 p2246 p2284 p2946 p3039 p3955 p4427 : Prop)
    (h40810 : (¬ p2027))
    (h10518 : p2027 ∨ (¬ p2187) ∨ (¬ p2246) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3039) ∨ (¬ p3955) ∨ (¬ p4427))
    : (¬ p2187) ∨ (¬ p2246) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3039) ∨ (¬ p3955) ∨ (¬ p4427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3039 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h10518 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41607 (p2027 p2553 p3641 p3660 p3822 p4610 p5220 : Prop)
    (h40810 : (¬ p2027))
    (h10519 : p2027 ∨ (¬ p2553) ∨ (¬ p3641) ∨ (¬ p3660) ∨ (¬ p3822) ∨ (¬ p4610) ∨ (¬ p5220))
    : (¬ p2553) ∨ (¬ p3641) ∨ (¬ p3660) ∨ (¬ p3822) ∨ (¬ p4610) ∨ (¬ p5220) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4610 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10519 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41608 (p2027 p3414 p3654 p3987 p4037 p4194 p4650 : Prop)
    (h40810 : (¬ p2027))
    (h10520 : p2027 ∨ (¬ p3414) ∨ (¬ p3654) ∨ (¬ p3987) ∨ (¬ p4037) ∨ (¬ p4194) ∨ (¬ p4650))
    : (¬ p3414) ∨ (¬ p3654) ∨ (¬ p3987) ∨ (¬ p4037) ∨ (¬ p4194) ∨ (¬ p4650) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3414 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10520 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41609 (p2027 p2284 p2589 p2659 p3413 p4110 : Prop)
    (h40810 : (¬ p2027))
    (h10521 : p2027 ∨ (¬ p2284) ∨ (¬ p2589) ∨ (¬ p2659) ∨ (¬ p3413) ∨ (¬ p4110))
    : (¬ p2284) ∨ (¬ p2589) ∨ (¬ p2659) ∨ (¬ p3413) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10521 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41610 (p2027 p2252 p2657 p2750 p3399 p3574 p3631 p3954 p4137 p4625 : Prop)
    (h40810 : (¬ p2027))
    (h10522 : p2027 ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3399) ∨ (¬ p3574) ∨ (¬ p3631) ∨ (¬ p3954) ∨ (¬ p4137) ∨ (¬ p4625))
    : (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3399) ∨ (¬ p3574) ∨ (¬ p3631) ∨ (¬ p3954) ∨ (¬ p4137) ∨ (¬ p4625) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h10522 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step41611 (p2027 p3193 p3246 p3399 p3461 p3571 p3954 p4425 p4625 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h10523 : p2027 ∨ (¬ p3193) ∨ (¬ p3246) ∨ (¬ p3399) ∨ (¬ p3461) ∨ (¬ p3571) ∨ (¬ p3954) ∨ (¬ p4425) ∨ (¬ p4625) ∨ (¬ p5216))
    : (¬ p3193) ∨ (¬ p3246) ∨ (¬ p3399) ∨ (¬ p3461) ∨ (¬ p3571) ∨ (¬ p3954) ∨ (¬ p4425) ∨ (¬ p4625) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3193 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3571 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h10523 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step41612 (p2027 p2579 p2659 p2797 p2810 p3984 : Prop)
    (h40810 : (¬ p2027))
    (h10524 : p2027 ∨ (¬ p2579) ∨ (¬ p2659) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3984))
    : (¬ p2579) ∨ (¬ p2659) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3984) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10524 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41614 (p2027 p3276 p4032 p4322 p4449 p4533 : Prop)
    (h40810 : (¬ p2027))
    (h10543 : p2027 ∨ (¬ p3276) ∨ (¬ p4032) ∨ (¬ p4322) ∨ (¬ p4449) ∨ (¬ p4533))
    : (¬ p3276) ∨ (¬ p4032) ∨ (¬ p4322) ∨ (¬ p4449) ∨ (¬ p4533) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10543 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41615 (p2027 p3399 p3576 p3585 p3954 p5086 : Prop)
    (h40810 : (¬ p2027))
    (h10544 : p2027 ∨ (¬ p3399) ∨ (¬ p3576) ∨ (¬ p3585) ∨ (¬ p3954) ∨ (¬ p5086))
    : (¬ p3399) ∨ (¬ p3576) ∨ (¬ p3585) ∨ (¬ p3954) ∨ (¬ p5086) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3576 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5086 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10544 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41617 (p2027 p3941 p4321 p4348 p5002 p5121 : Prop)
    (h40810 : (¬ p2027))
    (h10546 : p2027 ∨ (¬ p3941) ∨ (¬ p4321) ∨ (¬ p4348) ∨ (¬ p5002) ∨ (¬ p5121))
    : (¬ p3941) ∨ (¬ p4321) ∨ (¬ p4348) ∨ (¬ p5002) ∨ (¬ p5121) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3941 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4321 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5002 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5121 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10546 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41619 (p2027 p3115 p3680 p4321 p4938 p4957 : Prop)
    (h40810 : (¬ p2027))
    (h10548 : p2027 ∨ (¬ p3115) ∨ (¬ p3680) ∨ (¬ p4321) ∨ (¬ p4938) ∨ (¬ p4957))
    : (¬ p3115) ∨ (¬ p3680) ∨ (¬ p4321) ∨ (¬ p4938) ∨ (¬ p4957) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4321 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4938 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10548 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41620 (p2027 p2750 p3449 p3954 p4037 p4154 p4181 p4191 p5119 : Prop)
    (h40810 : (¬ p2027))
    (h10549 : p2027 ∨ (¬ p2750) ∨ (¬ p3449) ∨ (¬ p3954) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4181) ∨ (¬ p4191) ∨ (¬ p5119))
    : (¬ p2750) ∨ (¬ p3449) ∨ (¬ p3954) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4181) ∨ (¬ p4191) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2750 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4181 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h10549 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step41622 (p2027 p2187 p3399 p3631 p3744 p3923 p3954 p4625 p4870 : Prop)
    (h40810 : (¬ p2027))
    (h10551 : p2027 ∨ (¬ p2187) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3744) ∨ (¬ p3923) ∨ (¬ p3954) ∨ (¬ p4625) ∨ (¬ p4870))
    : (¬ p2187) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3744) ∨ (¬ p3923) ∨ (¬ p3954) ∨ (¬ p4625) ∨ (¬ p4870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h10551 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step41623 (p2027 p2810 p3365 p3471 p4325 p4652 : Prop)
    (h40810 : (¬ p2027))
    (h10552 : p2027 ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p3471) ∨ (¬ p4325) ∨ (¬ p4652))
    : (¬ p2810) ∨ (¬ p3365) ∨ (¬ p3471) ∨ (¬ p4325) ∨ (¬ p4652) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2810 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10552 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41624 (p2027 p2954 p3146 p3156 p3857 p4197 p4198 : Prop)
    (h40810 : (¬ p2027))
    (h10553 : p2027 ∨ (¬ p2954) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3857) ∨ (¬ p4197) ∨ (¬ p4198))
    : (¬ p2954) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3857) ∨ (¬ p4197) ∨ (¬ p4198) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2954 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10553 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41625 (p2027 p2190 p3146 p3923 p4347 p4514 : Prop)
    (h40810 : (¬ p2027))
    (h10554 : p2027 ∨ (¬ p2190) ∨ (¬ p3146) ∨ (¬ p3923) ∨ (¬ p4347) ∨ (¬ p4514))
    : (¬ p2190) ∨ (¬ p3146) ∨ (¬ p3923) ∨ (¬ p4347) ∨ (¬ p4514) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2190 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10554 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41626 (p2027 p2373 p3146 p3697 p3857 p4533 : Prop)
    (h40810 : (¬ p2027))
    (h10556 : p2027 ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p3697) ∨ (¬ p3857) ∨ (¬ p4533))
    : (¬ p2373) ∨ (¬ p3146) ∨ (¬ p3697) ∨ (¬ p3857) ∨ (¬ p4533) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10556 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41627 (p2027 p2553 p3097 p3660 p4173 p4629 : Prop)
    (h40810 : (¬ p2027))
    (h10557 : p2027 ∨ (¬ p2553) ∨ (¬ p3097) ∨ (¬ p3660) ∨ (¬ p4173) ∨ (¬ p4629))
    : (¬ p2553) ∨ (¬ p3097) ∨ (¬ p3660) ∨ (¬ p4173) ∨ (¬ p4629) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10557 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41628 (p2027 p2331 p2352 p3172 p4769 p4973 : Prop)
    (h40810 : (¬ p2027))
    (h10558 : p2027 ∨ (¬ p2331) ∨ (¬ p2352) ∨ (¬ p3172) ∨ (¬ p4769) ∨ (¬ p4973))
    : (¬ p2331) ∨ (¬ p2352) ∨ (¬ p3172) ∨ (¬ p4769) ∨ (¬ p4973) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4769 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10558 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41629 (p2027 p2298 p2331 p3309 p3414 p4761 : Prop)
    (h40810 : (¬ p2027))
    (h10559 : p2027 ∨ (¬ p2298) ∨ (¬ p2331) ∨ (¬ p3309) ∨ (¬ p3414) ∨ (¬ p4761))
    : (¬ p2298) ∨ (¬ p2331) ∨ (¬ p3309) ∨ (¬ p3414) ∨ (¬ p4761) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2298 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10559 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41630 (p2027 p2751 p2951 p2992 p3051 p4244 p4392 : Prop)
    (h40810 : (¬ p2027))
    (h10560 : p2027 ∨ (¬ p2751) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3051) ∨ (¬ p4244) ∨ (¬ p4392))
    : (¬ p2751) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3051) ∨ (¬ p4244) ∨ (¬ p4392) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2751 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10560 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41631 (p2027 p2137 p2156 p2553 p4244 p4275 p4718 : Prop)
    (h40810 : (¬ p2027))
    (h10561 : p2027 ∨ (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2553) ∨ (¬ p4244) ∨ (¬ p4275) ∨ (¬ p4718))
    : (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2553) ∨ (¬ p4244) ∨ (¬ p4275) ∨ (¬ p4718) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2137 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10561 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41632 (p2027 p2246 p2807 p3662 p4244 p4333 p4906 : Prop)
    (h40810 : (¬ p2027))
    (h10562 : p2027 ∨ (¬ p2246) ∨ (¬ p2807) ∨ (¬ p3662) ∨ (¬ p4244) ∨ (¬ p4333) ∨ (¬ p4906))
    : (¬ p2246) ∨ (¬ p2807) ∨ (¬ p3662) ∨ (¬ p4244) ∨ (¬ p4333) ∨ (¬ p4906) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10562 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41634 (p2027 p2352 p2860 p3694 p4115 p4170 p4718 : Prop)
    (h40810 : (¬ p2027))
    (h10564 : p2027 ∨ (¬ p2352) ∨ (¬ p2860) ∨ (¬ p3694) ∨ (¬ p4115) ∨ (¬ p4170) ∨ (¬ p4718))
    : (¬ p2352) ∨ (¬ p2860) ∨ (¬ p3694) ∨ (¬ p4115) ∨ (¬ p4170) ∨ (¬ p4718) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10564 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41636 (p2027 p2727 p3343 p3662 p3879 p4953 : Prop)
    (h40810 : (¬ p2027))
    (h10566 : p2027 ∨ (¬ p2727) ∨ (¬ p3343) ∨ (¬ p3662) ∨ (¬ p3879) ∨ (¬ p4953))
    : (¬ p2727) ∨ (¬ p3343) ∨ (¬ p3662) ∨ (¬ p3879) ∨ (¬ p4953) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10566 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41637 (p2027 p2387 p2577 p2662 p2819 p4315 p4426 p4701 : Prop)
    (h40810 : (¬ p2027))
    (h10567 : p2027 ∨ (¬ p2387) ∨ (¬ p2577) ∨ (¬ p2662) ∨ (¬ p2819) ∨ (¬ p4315) ∨ (¬ p4426) ∨ (¬ p4701))
    : (¬ p2387) ∨ (¬ p2577) ∨ (¬ p2662) ∨ (¬ p2819) ∨ (¬ p4315) ∨ (¬ p4426) ∨ (¬ p4701) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2387 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4701 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h10567 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41639 (p2027 p2295 p2860 p4244 p4275 p4560 : Prop)
    (h40810 : (¬ p2027))
    (h10569 : p2027 ∨ (¬ p2295) ∨ (¬ p2860) ∨ (¬ p4244) ∨ (¬ p4275) ∨ (¬ p4560))
    : (¬ p2295) ∨ (¬ p2860) ∨ (¬ p4244) ∨ (¬ p4275) ∨ (¬ p4560) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4560 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10569 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41640 (p2027 p2295 p2313 p3758 p4336 p4356 p4906 : Prop)
    (h40810 : (¬ p2027))
    (h10570 : p2027 ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p3758) ∨ (¬ p4336) ∨ (¬ p4356) ∨ (¬ p4906))
    : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p3758) ∨ (¬ p4336) ∨ (¬ p4356) ∨ (¬ p4906) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10570 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41642 (p2027 p2518 p3364 p3541 p3583 p3874 p5049 : Prop)
    (h40810 : (¬ p2027))
    (h10572 : p2027 ∨ (¬ p2518) ∨ (¬ p3364) ∨ (¬ p3541) ∨ (¬ p3583) ∨ (¬ p3874) ∨ (¬ p5049))
    : (¬ p2518) ∨ (¬ p3364) ∨ (¬ p3541) ∨ (¬ p3583) ∨ (¬ p3874) ∨ (¬ p5049) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5049 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10572 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41643 (p2027 p3027 p3662 p4244 p4333 p4906 : Prop)
    (h40810 : (¬ p2027))
    (h10573 : p2027 ∨ (¬ p3027) ∨ (¬ p3662) ∨ (¬ p4244) ∨ (¬ p4333) ∨ (¬ p4906))
    : (¬ p3027) ∨ (¬ p3662) ∨ (¬ p4244) ∨ (¬ p4333) ∨ (¬ p4906) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3027 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10573 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41644 (p2027 p3333 p3367 p3583 p3698 p4953 : Prop)
    (h40810 : (¬ p2027))
    (h10574 : p2027 ∨ (¬ p3333) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p4953))
    : (¬ p3333) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p4953) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10574 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41645 (p2027 p3367 p3641 p3688 p4342 p4598 : Prop)
    (h40810 : (¬ p2027))
    (h10575 : p2027 ∨ (¬ p3367) ∨ (¬ p3641) ∨ (¬ p3688) ∨ (¬ p4342) ∨ (¬ p4598))
    : (¬ p3367) ∨ (¬ p3641) ∨ (¬ p3688) ∨ (¬ p4342) ∨ (¬ p4598) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4342 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10575 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41646 (p2027 p2156 p3309 p3556 p4275 p4518 : Prop)
    (h40810 : (¬ p2027))
    (h10576 : p2027 ∨ (¬ p2156) ∨ (¬ p3309) ∨ (¬ p3556) ∨ (¬ p4275) ∨ (¬ p4518))
    : (¬ p2156) ∨ (¬ p3309) ∨ (¬ p3556) ∨ (¬ p4275) ∨ (¬ p4518) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10576 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41647 (p2027 p2996 p3189 p3551 p4378 p4851 : Prop)
    (h40810 : (¬ p2027))
    (h10577 : p2027 ∨ (¬ p2996) ∨ (¬ p3189) ∨ (¬ p3551) ∨ (¬ p4378) ∨ (¬ p4851))
    : (¬ p2996) ∨ (¬ p3189) ∨ (¬ p3551) ∨ (¬ p4378) ∨ (¬ p4851) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4378 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4851 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10577 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41648 (p2027 p2246 p2751 p2901 p2946 p4244 p4392 : Prop)
    (h40810 : (¬ p2027))
    (h10578 : p2027 ∨ (¬ p2246) ∨ (¬ p2751) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p4244) ∨ (¬ p4392))
    : (¬ p2246) ∨ (¬ p2751) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p4244) ∨ (¬ p4392) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10578 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41651 (p2027 p2440 p3842 p4111 p4953 p5175 : Prop)
    (h40810 : (¬ p2027))
    (h10581 : p2027 ∨ (¬ p2440) ∨ (¬ p3842) ∨ (¬ p4111) ∨ (¬ p4953) ∨ (¬ p5175))
    : (¬ p2440) ∨ (¬ p3842) ∨ (¬ p4111) ∨ (¬ p4953) ∨ (¬ p5175) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5175 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10581 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41652 (p2027 p2440 p3506 p4425 p4953 p5176 : Prop)
    (h40810 : (¬ p2027))
    (h10582 : p2027 ∨ (¬ p2440) ∨ (¬ p3506) ∨ (¬ p4425) ∨ (¬ p4953) ∨ (¬ p5176))
    : (¬ p2440) ∨ (¬ p3506) ∨ (¬ p4425) ∨ (¬ p4953) ∨ (¬ p5176) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5176 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10582 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41653 (p2027 p2177 p2247 p2307 p3848 p3941 p5017 p5119 p5284 : Prop)
    (h40810 : (¬ p2027))
    (h10583 : p2027 ∨ (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2307) ∨ (¬ p3848) ∨ (¬ p3941) ∨ (¬ p5017) ∨ (¬ p5119) ∨ (¬ p5284))
    : (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2307) ∨ (¬ p3848) ∨ (¬ p3941) ∨ (¬ p5017) ∨ (¬ p5119) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3848 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5017 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h10583 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step41654 (p2027 p2579 p3355 p3744 p4331 p4718 : Prop)
    (h40810 : (¬ p2027))
    (h10584 : p2027 ∨ (¬ p2579) ∨ (¬ p3355) ∨ (¬ p3744) ∨ (¬ p4331) ∨ (¬ p4718))
    : (¬ p2579) ∨ (¬ p3355) ∨ (¬ p3744) ∨ (¬ p4331) ∨ (¬ p4718) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10584 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41655 (p2027 p2501 p3343 p3574 p4026 p4331 : Prop)
    (h40810 : (¬ p2027))
    (h10585 : p2027 ∨ (¬ p2501) ∨ (¬ p3343) ∨ (¬ p3574) ∨ (¬ p4026) ∨ (¬ p4331))
    : (¬ p2501) ∨ (¬ p3343) ∨ (¬ p3574) ∨ (¬ p4026) ∨ (¬ p4331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2501 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4026 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10585 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41657 (p2027 p2440 p3019 p3319 p4137 p4319 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h10587 : p2027 ∨ (¬ p2440) ∨ (¬ p3019) ∨ (¬ p3319) ∨ (¬ p4137) ∨ (¬ p4319) ∨ (¬ p4717))
    : (¬ p2440) ∨ (¬ p3019) ∨ (¬ p3319) ∨ (¬ p4137) ∨ (¬ p4319) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10587 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41659 (p2027 p2386 p2505 p3238 p3319 p3946 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h10590 : p2027 ∨ (¬ p2386) ∨ (¬ p2505) ∨ (¬ p3238) ∨ (¬ p3319) ∨ (¬ p3946) ∨ (¬ p4717))
    : (¬ p2386) ∨ (¬ p2505) ∨ (¬ p3238) ∨ (¬ p3319) ∨ (¬ p3946) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2386 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10590 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41660 (p2027 p3233 p3238 p3707 p4953 p5175 p5284 : Prop)
    (h40810 : (¬ p2027))
    (h10591 : p2027 ∨ (¬ p3233) ∨ (¬ p3238) ∨ (¬ p3707) ∨ (¬ p4953) ∨ (¬ p5175) ∨ (¬ p5284))
    : (¬ p3233) ∨ (¬ p3238) ∨ (¬ p3707) ∨ (¬ p4953) ∨ (¬ p5175) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3233 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5175 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10591 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41661 (p2027 p2440 p2505 p3063 p3956 p4116 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h10592 : p2027 ∨ (¬ p2440) ∨ (¬ p2505) ∨ (¬ p3063) ∨ (¬ p3956) ∨ (¬ p4116) ∨ (¬ p4717))
    : (¬ p2440) ∨ (¬ p2505) ∨ (¬ p3063) ∨ (¬ p3956) ∨ (¬ p4116) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10592 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41665 (p2027 p2295 p3324 p3791 p4138 p5564 : Prop)
    (h40810 : (¬ p2027))
    (h10600 : p2027 ∨ (¬ p2295) ∨ (¬ p3324) ∨ (¬ p3791) ∨ (¬ p4138) ∨ (¬ p5564))
    : (¬ p2295) ∨ (¬ p3324) ∨ (¬ p3791) ∨ (¬ p4138) ∨ (¬ p5564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10600 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41666 (p2027 p2088 p3156 p3696 p4261 p4492 p4957 : Prop)
    (h40810 : (¬ p2027))
    (h10601 : p2027 ∨ (¬ p2088) ∨ (¬ p3156) ∨ (¬ p3696) ∨ (¬ p4261) ∨ (¬ p4492) ∨ (¬ p4957))
    : (¬ p2088) ∨ (¬ p3156) ∨ (¬ p3696) ∨ (¬ p4261) ∨ (¬ p4492) ∨ (¬ p4957) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4492 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10601 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41667 (p2027 p2138 p2241 p2750 p2839 p3873 : Prop)
    (h40810 : (¬ p2027))
    (h10602 : p2027 ∨ (¬ p2138) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2839) ∨ (¬ p3873))
    : (¬ p2138) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2839) ∨ (¬ p3873) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10602 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41668 (p2027 p2132 p2657 p2870 p2881 p3742 p4278 p4666 p4789 : Prop)
    (h40810 : (¬ p2027))
    (h10603 : p2027 ∨ (¬ p2132) ∨ (¬ p2657) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p4789))
    : (¬ p2132) ∨ (¬ p2657) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p4789) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h10603 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step41671 (p2027 p3323 p3324 p3692 p4345 p4433 : Prop)
    (h40810 : (¬ p2027))
    (h10606 : p2027 ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p3692) ∨ (¬ p4345) ∨ (¬ p4433))
    : (¬ p3323) ∨ (¬ p3324) ∨ (¬ p3692) ∨ (¬ p4345) ∨ (¬ p4433) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4345 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10606 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41672 (p2027 p3276 p3358 p3692 p4434 p4444 : Prop)
    (h40810 : (¬ p2027))
    (h10607 : p2027 ∨ (¬ p3276) ∨ (¬ p3358) ∨ (¬ p3692) ∨ (¬ p4434) ∨ (¬ p4444))
    : (¬ p3276) ∨ (¬ p3358) ∨ (¬ p3692) ∨ (¬ p4434) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10607 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41673 (p2027 p2210 p2619 p3860 p3906 p4875 : Prop)
    (h40810 : (¬ p2027))
    (h10608 : p2027 ∨ (¬ p2210) ∨ (¬ p2619) ∨ (¬ p3860) ∨ (¬ p3906) ∨ (¬ p4875))
    : (¬ p2210) ∨ (¬ p2619) ∨ (¬ p3860) ∨ (¬ p3906) ∨ (¬ p4875) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10608 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41674 (p2027 p2144 p2220 p2252 p2657 p2750 p2753 p3146 p3266 p3742 p4831 p5503 : Prop)
    (h40810 : (¬ p2027))
    (h10609 : p2027 ∨ (¬ p2144) ∨ (¬ p2220) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p3742) ∨ (¬ p4831) ∨ (¬ p5503))
    : (¬ p2144) ∨ (¬ p2220) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p3742) ∨ (¬ p4831) ∨ (¬ p5503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2144 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h10609 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step41675 (p2027 p2727 p2751 p3343 p3364 p5160 : Prop)
    (h40810 : (¬ p2027))
    (h10611 : p2027 ∨ (¬ p2727) ∨ (¬ p2751) ∨ (¬ p3343) ∨ (¬ p3364) ∨ (¬ p5160))
    : (¬ p2727) ∨ (¬ p2751) ∨ (¬ p3343) ∨ (¬ p3364) ∨ (¬ p5160) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10611 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41676 (p2027 p2363 p3325 p4053 p4261 p4371 p5477 : Prop)
    (h40810 : (¬ p2027))
    (h10612 : p2027 ∨ (¬ p2363) ∨ (¬ p3325) ∨ (¬ p4053) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p5477))
    : (¬ p2363) ∨ (¬ p3325) ∨ (¬ p4053) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p5477) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10612 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41678 (p2027 p2187 p2493 p2928 p3921 p4203 p4405 : Prop)
    (h40810 : (¬ p2027))
    (h10614 : p2027 ∨ (¬ p2187) ∨ (¬ p2493) ∨ (¬ p2928) ∨ (¬ p3921) ∨ (¬ p4203) ∨ (¬ p4405))
    : (¬ p2187) ∨ (¬ p2493) ∨ (¬ p2928) ∨ (¬ p3921) ∨ (¬ p4203) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10614 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41680 (p2027 p2241 p2745 p2797 p3591 p4319 : Prop)
    (h40810 : (¬ p2027))
    (h10617 : p2027 ∨ (¬ p2241) ∨ (¬ p2745) ∨ (¬ p2797) ∨ (¬ p3591) ∨ (¬ p4319))
    : (¬ p2241) ∨ (¬ p2745) ∨ (¬ p2797) ∨ (¬ p3591) ∨ (¬ p4319) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10617 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41683 (p2027 p2505 p3063 p3238 p3956 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h10621 : p2027 ∨ (¬ p2505) ∨ (¬ p3063) ∨ (¬ p3238) ∨ (¬ p3956) ∨ (¬ p4717))
    : (¬ p2505) ∨ (¬ p3063) ∨ (¬ p3238) ∨ (¬ p3956) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2505 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10621 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41685 (p2027 p2341 p2589 p3644 p4646 p5201 : Prop)
    (h40810 : (¬ p2027))
    (h10623 : p2027 ∨ (¬ p2341) ∨ (¬ p2589) ∨ (¬ p3644) ∨ (¬ p4646) ∨ (¬ p5201))
    : (¬ p2341) ∨ (¬ p2589) ∨ (¬ p3644) ∨ (¬ p4646) ∨ (¬ p5201) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10623 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41686 (p2027 p2177 p2476 p3389 p4276 p4383 : Prop)
    (h40810 : (¬ p2027))
    (h10624 : p2027 ∨ (¬ p2177) ∨ (¬ p2476) ∨ (¬ p3389) ∨ (¬ p4276) ∨ (¬ p4383))
    : (¬ p2177) ∨ (¬ p2476) ∨ (¬ p3389) ∨ (¬ p4276) ∨ (¬ p4383) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10624 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41687 (p2027 p2963 p3166 p3568 p4405 p4417 : Prop)
    (h40810 : (¬ p2027))
    (h10625 : p2027 ∨ (¬ p2963) ∨ (¬ p3166) ∨ (¬ p3568) ∨ (¬ p4405) ∨ (¬ p4417))
    : (¬ p2963) ∨ (¬ p3166) ∨ (¬ p3568) ∨ (¬ p4405) ∨ (¬ p4417) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2963 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10625 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41688 (p2027 p2166 p2573 p3904 p4034 p4120 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h10626 : p2027 ∨ (¬ p2166) ∨ (¬ p2573) ∨ (¬ p3904) ∨ (¬ p4034) ∨ (¬ p4120) ∨ (¬ p4717))
    : (¬ p2166) ∨ (¬ p2573) ∨ (¬ p3904) ∨ (¬ p4034) ∨ (¬ p4120) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4034 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10626 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41690 (p2027 p2295 p2573 p3540 p3921 p4976 : Prop)
    (h40810 : (¬ p2027))
    (h10628 : p2027 ∨ (¬ p2295) ∨ (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3921) ∨ (¬ p4976))
    : (¬ p2295) ∨ (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3921) ∨ (¬ p4976) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4976 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10628 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41691 (p2027 p2417 p2437 p2926 p3817 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h10629 : p2027 ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2926) ∨ (¬ p3817) ∨ (¬ p4811))
    : (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2926) ∨ (¬ p3817) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2926 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10629 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41692 (p2027 p2504 p3093 p3238 p3452 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h10630 : p2027 ∨ (¬ p2504) ∨ (¬ p3093) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4717))
    : (¬ p2504) ∨ (¬ p3093) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2504 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10630 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41693 (p2027 p2563 p3355 p3646 p3904 p4953 : Prop)
    (h40810 : (¬ p2027))
    (h10631 : p2027 ∨ (¬ p2563) ∨ (¬ p3355) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4953))
    : (¬ p2563) ∨ (¬ p3355) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4953) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10631 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41694 (p2027 p2440 p3449 p3452 p4116 p4610 p4687 : Prop)
    (h40810 : (¬ p2027))
    (h10632 : p2027 ∨ (¬ p2440) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4116) ∨ (¬ p4610) ∨ (¬ p4687))
    : (¬ p2440) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4116) ∨ (¬ p4610) ∨ (¬ p4687) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4610 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4687 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10632 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41696 (p2027 p2608 p2891 p3369 p3556 p4377 : Prop)
    (h40810 : (¬ p2027))
    (h10634 : p2027 ∨ (¬ p2608) ∨ (¬ p2891) ∨ (¬ p3369) ∨ (¬ p3556) ∨ (¬ p4377))
    : (¬ p2608) ∨ (¬ p2891) ∨ (¬ p3369) ∨ (¬ p3556) ∨ (¬ p4377) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3369 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10634 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41697 (p2027 p2476 p3355 p3692 p4434 p4695 : Prop)
    (h40810 : (¬ p2027))
    (h10635 : p2027 ∨ (¬ p2476) ∨ (¬ p3355) ∨ (¬ p3692) ∨ (¬ p4434) ∨ (¬ p4695))
    : (¬ p2476) ∨ (¬ p3355) ∨ (¬ p3692) ∨ (¬ p4434) ∨ (¬ p4695) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2476 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10635 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41698 (p2027 p2177 p3146 p4107 p4445 p4905 : Prop)
    (h40810 : (¬ p2027))
    (h10636 : p2027 ∨ (¬ p2177) ∨ (¬ p3146) ∨ (¬ p4107) ∨ (¬ p4445) ∨ (¬ p4905))
    : (¬ p2177) ∨ (¬ p3146) ∨ (¬ p4107) ∨ (¬ p4445) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10636 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41699 (p2027 p3256 p3644 p4044 p4348 p4653 : Prop)
    (h40810 : (¬ p2027))
    (h10637 : p2027 ∨ (¬ p3256) ∨ (¬ p3644) ∨ (¬ p4044) ∨ (¬ p4348) ∨ (¬ p4653))
    : (¬ p3256) ∨ (¬ p3644) ∨ (¬ p4044) ∨ (¬ p4348) ∨ (¬ p4653) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4653 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10637 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41700 (p2027 p2363 p3325 p3644 p4118 p4276 p4378 : Prop)
    (h40810 : (¬ p2027))
    (h10638 : p2027 ∨ (¬ p2363) ∨ (¬ p3325) ∨ (¬ p3644) ∨ (¬ p4118) ∨ (¬ p4276) ∨ (¬ p4378))
    : (¬ p2363) ∨ (¬ p3325) ∨ (¬ p3644) ∨ (¬ p4118) ∨ (¬ p4276) ∨ (¬ p4378) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4378 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10638 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41701 (p2027 p2810 p3434 p3947 p4652 p4781 : Prop)
    (h40810 : (¬ p2027))
    (h10639 : p2027 ∨ (¬ p2810) ∨ (¬ p3434) ∨ (¬ p3947) ∨ (¬ p4652) ∨ (¬ p4781))
    : (¬ p2810) ∨ (¬ p3434) ∨ (¬ p3947) ∨ (¬ p4652) ∨ (¬ p4781) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2810 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10639 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41702 (p2027 p2177 p3027 p4360 p4548 p4570 : Prop)
    (h40810 : (¬ p2027))
    (h10640 : p2027 ∨ (¬ p2177) ∨ (¬ p3027) ∨ (¬ p4360) ∨ (¬ p4548) ∨ (¬ p4570))
    : (¬ p2177) ∨ (¬ p3027) ∨ (¬ p4360) ∨ (¬ p4548) ∨ (¬ p4570) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10640 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41703 (p2027 p2341 p2441 p2870 p3644 p3691 p4885 : Prop)
    (h40810 : (¬ p2027))
    (h10641 : p2027 ∨ (¬ p2341) ∨ (¬ p2441) ∨ (¬ p2870) ∨ (¬ p3644) ∨ (¬ p3691) ∨ (¬ p4885))
    : (¬ p2341) ∨ (¬ p2441) ∨ (¬ p2870) ∨ (¬ p3644) ∨ (¬ p3691) ∨ (¬ p4885) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10641 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41704 (p2027 p3097 p3125 p4276 p4278 p4623 : Prop)
    (h40810 : (¬ p2027))
    (h10642 : p2027 ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p4276) ∨ (¬ p4278) ∨ (¬ p4623))
    : (¬ p3097) ∨ (¬ p3125) ∨ (¬ p4276) ∨ (¬ p4278) ∨ (¬ p4623) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3097 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4623 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10642 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41705 (p2027 p2088 p2313 p4114 p4347 p4405 : Prop)
    (h40810 : (¬ p2027))
    (h10643 : p2027 ∨ (¬ p2088) ∨ (¬ p2313) ∨ (¬ p4114) ∨ (¬ p4347) ∨ (¬ p4405))
    : (¬ p2088) ∨ (¬ p2313) ∨ (¬ p4114) ∨ (¬ p4347) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4114 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10643 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41706 (p2027 p2510 p2528 p2588 p3857 p4113 p4405 : Prop)
    (h40810 : (¬ p2027))
    (h10644 : p2027 ∨ (¬ p2510) ∨ (¬ p2528) ∨ (¬ p2588) ∨ (¬ p3857) ∨ (¬ p4113) ∨ (¬ p4405))
    : (¬ p2510) ∨ (¬ p2528) ∨ (¬ p2588) ∨ (¬ p3857) ∨ (¬ p4113) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2510 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4113 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10644 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41707 (p2027 p2927 p3201 p3379 p4366 p5214 : Prop)
    (h40810 : (¬ p2027))
    (h10645 : p2027 ∨ (¬ p2927) ∨ (¬ p3201) ∨ (¬ p3379) ∨ (¬ p4366) ∨ (¬ p5214))
    : (¬ p2927) ∨ (¬ p3201) ∨ (¬ p3379) ∨ (¬ p4366) ∨ (¬ p5214) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2927 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5214 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10645 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41708 (p2027 p2437 p2928 p2992 p3402 p4704 : Prop)
    (h40810 : (¬ p2027))
    (h10646 : p2027 ∨ (¬ p2437) ∨ (¬ p2928) ∨ (¬ p2992) ∨ (¬ p3402) ∨ (¬ p4704))
    : (¬ p2437) ∨ (¬ p2928) ∨ (¬ p2992) ∨ (¬ p3402) ∨ (¬ p4704) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4704 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10646 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41709 (p2027 p2573 p2589 p3952 p4203 p4702 : Prop)
    (h40810 : (¬ p2027))
    (h10647 : p2027 ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3952) ∨ (¬ p4203) ∨ (¬ p4702))
    : (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3952) ∨ (¬ p4203) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10647 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41710 (p2027 p2247 p2608 p2742 p2829 p4845 : Prop)
    (h40810 : (¬ p2027))
    (h10648 : p2027 ∨ (¬ p2247) ∨ (¬ p2608) ∨ (¬ p2742) ∨ (¬ p2829) ∨ (¬ p4845))
    : (¬ p2247) ∨ (¬ p2608) ∨ (¬ p2742) ∨ (¬ p2829) ∨ (¬ p4845) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4845 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10648 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41711 (p2027 p2313 p2383 p3550 p3644 p4276 : Prop)
    (h40810 : (¬ p2027))
    (h10649 : p2027 ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p3550) ∨ (¬ p3644) ∨ (¬ p4276))
    : (¬ p2313) ∨ (¬ p2383) ∨ (¬ p3550) ∨ (¬ p3644) ∨ (¬ p4276) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10649 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41712 (p2027 p2373 p3016 p3497 p4700 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h10667 : p2027 ∨ (¬ p2373) ∨ (¬ p3016) ∨ (¬ p3497) ∨ (¬ p4700) ∨ (¬ p4717))
    : (¬ p2373) ∨ (¬ p3016) ∨ (¬ p3497) ∨ (¬ p4700) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10667 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41713 (p2027 p2341 p2437 p4256 p4383 p5203 : Prop)
    (h40810 : (¬ p2027))
    (h10668 : p2027 ∨ (¬ p2341) ∨ (¬ p2437) ∨ (¬ p4256) ∨ (¬ p4383) ∨ (¬ p5203))
    : (¬ p2341) ∨ (¬ p2437) ∨ (¬ p4256) ∨ (¬ p4383) ∨ (¬ p5203) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10668 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41714 (p2027 p3093 p3452 p3590 p3874 p3922 p3984 p4595 : Prop)
    (h40810 : (¬ p2027))
    (h10669 : p2027 ∨ (¬ p3093) ∨ (¬ p3452) ∨ (¬ p3590) ∨ (¬ p3874) ∨ (¬ p3922) ∨ (¬ p3984) ∨ (¬ p4595))
    : (¬ p3093) ∨ (¬ p3452) ∨ (¬ p3590) ∨ (¬ p3874) ∨ (¬ p3922) ∨ (¬ p3984) ∨ (¬ p4595) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3093 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4595 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h10669 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41715 (p2027 p3483 p3822 p3947 p4570 p5299 p5379 : Prop)
    (h40810 : (¬ p2027))
    (h10670 : p2027 ∨ (¬ p3483) ∨ (¬ p3822) ∨ (¬ p3947) ∨ (¬ p4570) ∨ (¬ p5299) ∨ (¬ p5379))
    : (¬ p3483) ∨ (¬ p3822) ∨ (¬ p3947) ∨ (¬ p4570) ∨ (¬ p5299) ∨ (¬ p5379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5299 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10670 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41716 (p2027 p2122 p2312 p3516 p3947 p4067 p4846 : Prop)
    (h40810 : (¬ p2027))
    (h10671 : p2027 ∨ (¬ p2122) ∨ (¬ p2312) ∨ (¬ p3516) ∨ (¬ p3947) ∨ (¬ p4067) ∨ (¬ p4846))
    : (¬ p2122) ∨ (¬ p2312) ∨ (¬ p3516) ∨ (¬ p3947) ∨ (¬ p4067) ∨ (¬ p4846) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4846 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10671 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41717 (p2027 p2299 p2396 p3692 p4443 p4902 : Prop)
    (h40810 : (¬ p2027))
    (h10672 : p2027 ∨ (¬ p2299) ∨ (¬ p2396) ∨ (¬ p3692) ∨ (¬ p4443) ∨ (¬ p4902))
    : (¬ p2299) ∨ (¬ p2396) ∨ (¬ p3692) ∨ (¬ p4443) ∨ (¬ p4902) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4443 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10672 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41718 (p2027 p2187 p3097 p3550 p3644 p4276 : Prop)
    (h40810 : (¬ p2027))
    (h10673 : p2027 ∨ (¬ p2187) ∨ (¬ p3097) ∨ (¬ p3550) ∨ (¬ p3644) ∨ (¬ p4276))
    : (¬ p2187) ∨ (¬ p3097) ∨ (¬ p3550) ∨ (¬ p3644) ∨ (¬ p4276) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10673 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41719 (p2027 p2589 p3516 p3947 p3984 p4067 p4717 p5201 : Prop)
    (h40810 : (¬ p2027))
    (h10674 : p2027 ∨ (¬ p2589) ∨ (¬ p3516) ∨ (¬ p3947) ∨ (¬ p3984) ∨ (¬ p4067) ∨ (¬ p4717) ∨ (¬ p5201))
    : (¬ p2589) ∨ (¬ p3516) ∨ (¬ p3947) ∨ (¬ p3984) ∨ (¬ p4067) ∨ (¬ p4717) ∨ (¬ p5201) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h10674 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41720 (p2027 p3641 p3969 p4158 p5670 p5681 : Prop)
    (h40810 : (¬ p2027))
    (h10675 : p2027 ∨ (¬ p3641) ∨ (¬ p3969) ∨ (¬ p4158) ∨ (¬ p5670) ∨ (¬ p5681))
    : (¬ p3641) ∨ (¬ p3969) ∨ (¬ p4158) ∨ (¬ p5670) ∨ (¬ p5681) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4158 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5681 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10675 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41722 (p2027 p2177 p3919 p3941 p4570 p5600 : Prop)
    (h40810 : (¬ p2027))
    (h10677 : p2027 ∨ (¬ p2177) ∨ (¬ p3919) ∨ (¬ p3941) ∨ (¬ p4570) ∨ (¬ p5600))
    : (¬ p2177) ∨ (¬ p3919) ∨ (¬ p3941) ∨ (¬ p4570) ∨ (¬ p5600) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10677 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41723 (p2027 p2177 p2761 p3945 p4429 p4570 p5284 : Prop)
    (h40810 : (¬ p2027))
    (h10678 : p2027 ∨ (¬ p2177) ∨ (¬ p2761) ∨ (¬ p3945) ∨ (¬ p4429) ∨ (¬ p4570) ∨ (¬ p5284))
    : (¬ p2177) ∨ (¬ p2761) ∨ (¬ p3945) ∨ (¬ p4429) ∨ (¬ p4570) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3945 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4429 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10678 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41724 (p2027 p2177 p2459 p3919 p4118 p4570 : Prop)
    (h40810 : (¬ p2027))
    (h10679 : p2027 ∨ (¬ p2177) ∨ (¬ p2459) ∨ (¬ p3919) ∨ (¬ p4118) ∨ (¬ p4570))
    : (¬ p2177) ∨ (¬ p2459) ∨ (¬ p3919) ∨ (¬ p4118) ∨ (¬ p4570) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10679 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41725 (p2027 p2177 p2311 p3309 p3551 p5018 : Prop)
    (h40810 : (¬ p2027))
    (h10680 : p2027 ∨ (¬ p2177) ∨ (¬ p2311) ∨ (¬ p3309) ∨ (¬ p3551) ∨ (¬ p5018))
    : (¬ p2177) ∨ (¬ p2311) ∨ (¬ p3309) ∨ (¬ p3551) ∨ (¬ p5018) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5018 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10680 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41726 (p2027 p2396 p2807 p3292 p3579 p4276 p4656 : Prop)
    (h40810 : (¬ p2027))
    (h10681 : p2027 ∨ (¬ p2396) ∨ (¬ p2807) ∨ (¬ p3292) ∨ (¬ p3579) ∨ (¬ p4276) ∨ (¬ p4656))
    : (¬ p2396) ∨ (¬ p2807) ∨ (¬ p3292) ∨ (¬ p3579) ∨ (¬ p4276) ∨ (¬ p4656) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3292 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10681 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41727 (p2027 p2311 p3631 p3821 p4110 p4356 p4431 p4632 : Prop)
    (h40810 : (¬ p2027))
    (h10682 : p2027 ∨ (¬ p2311) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4110) ∨ (¬ p4356) ∨ (¬ p4431) ∨ (¬ p4632))
    : (¬ p2311) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4110) ∨ (¬ p4356) ∨ (¬ p4431) ∨ (¬ p4632) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2311 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h10682 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41728 (p2027 p3434 p3587 p3821 p4235 p4283 p4885 : Prop)
    (h40810 : (¬ p2027))
    (h10683 : p2027 ∨ (¬ p3434) ∨ (¬ p3587) ∨ (¬ p3821) ∨ (¬ p4235) ∨ (¬ p4283) ∨ (¬ p4885))
    : (¬ p3434) ∨ (¬ p3587) ∨ (¬ p3821) ∨ (¬ p4235) ∨ (¬ p4283) ∨ (¬ p4885) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3587 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10683 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41729 (p2027 p2187 p2192 p2590 p3324 p3984 p4632 : Prop)
    (h40810 : (¬ p2027))
    (h10684 : p2027 ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2590) ∨ (¬ p3324) ∨ (¬ p3984) ∨ (¬ p4632))
    : (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2590) ∨ (¬ p3324) ∨ (¬ p3984) ∨ (¬ p4632) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10684 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41730 (p2027 p2891 p2946 p3414 p3699 p4960 : Prop)
    (h40810 : (¬ p2027))
    (h10685 : p2027 ∨ (¬ p2891) ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3699) ∨ (¬ p4960))
    : (¬ p2891) ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3699) ∨ (¬ p4960) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3699 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10685 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41731 (p2027 p2220 p2657 p2958 p3497 p4704 : Prop)
    (h40810 : (¬ p2027))
    (h10686 : p2027 ∨ (¬ p2220) ∨ (¬ p2657) ∨ (¬ p2958) ∨ (¬ p3497) ∨ (¬ p4704))
    : (¬ p2220) ∨ (¬ p2657) ∨ (¬ p2958) ∨ (¬ p3497) ∨ (¬ p4704) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4704 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10686 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41732 (p2027 p2441 p2881 p2891 p3644 p4632 : Prop)
    (h40810 : (¬ p2027))
    (h10687 : p2027 ∨ (¬ p2441) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3644) ∨ (¬ p4632))
    : (¬ p2441) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3644) ∨ (¬ p4632) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2441 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10687 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41735 (p2027 p2656 p2727 p2751 p3364 p3389 p3876 : Prop)
    (h40810 : (¬ p2027))
    (h10691 : p2027 ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2751) ∨ (¬ p3364) ∨ (¬ p3389) ∨ (¬ p3876))
    : (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2751) ∨ (¬ p3364) ∨ (¬ p3389) ∨ (¬ p3876) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2656 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10691 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41736 (p2027 p2192 p2274 p2588 p2590 p4632 : Prop)
    (h40810 : (¬ p2027))
    (h10692 : p2027 ∨ (¬ p2192) ∨ (¬ p2274) ∨ (¬ p2588) ∨ (¬ p2590) ∨ (¬ p4632))
    : (¬ p2192) ∨ (¬ p2274) ∨ (¬ p2588) ∨ (¬ p2590) ∨ (¬ p4632) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10692 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41737 (p2027 p2470 p3097 p3201 p3555 p3874 p4173 p4276 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h10693 : p2027 ∨ (¬ p2470) ∨ (¬ p3097) ∨ (¬ p3201) ∨ (¬ p3555) ∨ (¬ p3874) ∨ (¬ p4173) ∨ (¬ p4276) ∨ (¬ p5190))
    : (¬ p2470) ∨ (¬ p3097) ∨ (¬ p3201) ∨ (¬ p3555) ∨ (¬ p3874) ∨ (¬ p4173) ∨ (¬ p4276) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h10693 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step41738 (p2027 p2246 p2264 p2946 p3031 p3548 p3580 p4704 : Prop)
    (h40810 : (¬ p2027))
    (h10694 : p2027 ∨ (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2946) ∨ (¬ p3031) ∨ (¬ p3548) ∨ (¬ p3580) ∨ (¬ p4704))
    : (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2946) ∨ (¬ p3031) ∨ (¬ p3548) ∨ (¬ p3580) ∨ (¬ p4704) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4704 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h10694 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41740 (p2027 p2533 p3680 p4348 p4444 p4905 : Prop)
    (h40810 : (¬ p2027))
    (h10696 : p2027 ∨ (¬ p2533) ∨ (¬ p3680) ∨ (¬ p4348) ∨ (¬ p4444) ∨ (¬ p4905))
    : (¬ p2533) ∨ (¬ p3680) ∨ (¬ p4348) ∨ (¬ p4444) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2533 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10696 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41742 (p2027 p2192 p3952 p4111 p4365 p4704 : Prop)
    (h40810 : (¬ p2027))
    (h10698 : p2027 ∨ (¬ p2192) ∨ (¬ p3952) ∨ (¬ p4111) ∨ (¬ p4365) ∨ (¬ p4704))
    : (¬ p2192) ∨ (¬ p3952) ∨ (¬ p4111) ∨ (¬ p4365) ∨ (¬ p4704) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4704 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10698 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41743 (p2027 p2166 p2957 p4111 p4120 p4365 p4704 : Prop)
    (h40810 : (¬ p2027))
    (h10699 : p2027 ∨ (¬ p2166) ∨ (¬ p2957) ∨ (¬ p4111) ∨ (¬ p4120) ∨ (¬ p4365) ∨ (¬ p4704))
    : (¬ p2166) ∨ (¬ p2957) ∨ (¬ p4111) ∨ (¬ p4120) ∨ (¬ p4365) ∨ (¬ p4704) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4704 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10699 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41744 (p2027 p2656 p3136 p3364 p3389 p3876 p4704 : Prop)
    (h40810 : (¬ p2027))
    (h10700 : p2027 ∨ (¬ p2656) ∨ (¬ p3136) ∨ (¬ p3364) ∨ (¬ p3389) ∨ (¬ p3876) ∨ (¬ p4704))
    : (¬ p2656) ∨ (¬ p3136) ∨ (¬ p3364) ∨ (¬ p3389) ∨ (¬ p3876) ∨ (¬ p4704) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2656 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4704 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10700 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41745 (p2027 p2534 p3125 p3989 p4345 p4596 : Prop)
    (h40810 : (¬ p2027))
    (h10701 : p2027 ∨ (¬ p2534) ∨ (¬ p3125) ∨ (¬ p3989) ∨ (¬ p4345) ∨ (¬ p4596))
    : (¬ p2534) ∨ (¬ p3125) ∨ (¬ p3989) ∨ (¬ p4345) ∨ (¬ p4596) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2534 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4345 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10701 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41746 (p2027 p2751 p4053 p4195 p4759 p5717 : Prop)
    (h40810 : (¬ p2027))
    (h10702 : p2027 ∨ (¬ p2751) ∨ (¬ p4053) ∨ (¬ p4195) ∨ (¬ p4759) ∨ (¬ p5717))
    : (¬ p2751) ∨ (¬ p4053) ∨ (¬ p4195) ∨ (¬ p4759) ∨ (¬ p5717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2751 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10702 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41747 (p2027 p3389 p3555 p3641 p3876 p3989 p4173 p4596 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h10703 : p2027 ∨ (¬ p3389) ∨ (¬ p3555) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4596) ∨ (¬ p5190))
    : (¬ p3389) ∨ (¬ p3555) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4596) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h10703 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step41748 (p2027 p2246 p3286 p4041 p4348 p4350 p4360 : Prop)
    (h40810 : (¬ p2027))
    (h10704 : p2027 ∨ (¬ p2246) ∨ (¬ p3286) ∨ (¬ p4041) ∨ (¬ p4348) ∨ (¬ p4350) ∨ (¬ p4360))
    : (¬ p2246) ∨ (¬ p3286) ∨ (¬ p4041) ∨ (¬ p4348) ∨ (¬ p4350) ∨ (¬ p4360) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4350 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10704 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41749 (p2027 p2810 p3105 p4208 p4313 p4704 : Prop)
    (h40810 : (¬ p2027))
    (h10705 : p2027 ∨ (¬ p2810) ∨ (¬ p3105) ∨ (¬ p4208) ∨ (¬ p4313) ∨ (¬ p4704))
    : (¬ p2810) ∨ (¬ p3105) ∨ (¬ p4208) ∨ (¬ p4313) ∨ (¬ p4704) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2810 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4704 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10705 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41750 (p2027 p2230 p2656 p2727 p2751 p3364 p3684 : Prop)
    (h40810 : (¬ p2027))
    (h10706 : p2027 ∨ (¬ p2230) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2751) ∨ (¬ p3364) ∨ (¬ p3684))
    : (¬ p2230) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2751) ∨ (¬ p3364) ∨ (¬ p3684) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10706 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41751 (p2027 p2307 p2584 p2588 p3584 p4730 : Prop)
    (h40810 : (¬ p2027))
    (h10707 : p2027 ∨ (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p3584) ∨ (¬ p4730))
    : (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p3584) ∨ (¬ p4730) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10707 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41754 (p2027 p3105 p4244 p4277 p4278 p4323 p5299 : Prop)
    (h40810 : (¬ p2027))
    (h10712 : p2027 ∨ (¬ p3105) ∨ (¬ p4244) ∨ (¬ p4277) ∨ (¬ p4278) ∨ (¬ p4323) ∨ (¬ p5299))
    : (¬ p3105) ∨ (¬ p4244) ∨ (¬ p4277) ∨ (¬ p4278) ∨ (¬ p4323) ∨ (¬ p5299) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5299 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10712 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41755 (p2027 p2563 p2850 p3646 p3904 p4727 : Prop)
    (h40810 : (¬ p2027))
    (h10713 : p2027 ∨ (¬ p2563) ∨ (¬ p2850) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4727))
    : (¬ p2563) ∨ (¬ p2850) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10713 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41756 (p2027 p2396 p3399 p3834 p5142 p5358 : Prop)
    (h40810 : (¬ p2027))
    (h10714 : p2027 ∨ (¬ p2396) ∨ (¬ p3399) ∨ (¬ p3834) ∨ (¬ p5142) ∨ (¬ p5358))
    : (¬ p2396) ∨ (¬ p3399) ∨ (¬ p3834) ∨ (¬ p5142) ∨ (¬ p5358) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3834 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5142 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10714 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41758 (p2027 p2210 p3583 p3954 p4875 : Prop)
    (h40810 : (¬ p2027))
    (h10717 : p2027 ∨ (¬ p2210) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p4875))
    : (¬ p2210) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p4875) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2027) := h40810;
    (Or.elim h10717 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step41759 (p2027 p3631 p3767 p4322 p4402 p4914 p5295 : Prop)
    (h40810 : (¬ p2027))
    (h10718 : p2027 ∨ (¬ p3631) ∨ (¬ p3767) ∨ (¬ p4322) ∨ (¬ p4402) ∨ (¬ p4914) ∨ (¬ p5295))
    : (¬ p3631) ∨ (¬ p3767) ∨ (¬ p4322) ∨ (¬ p4402) ∨ (¬ p4914) ∨ (¬ p5295) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4914 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10718 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41760 (p2027 p2685 p3246 p3297 p4035 p4280 p5295 : Prop)
    (h40810 : (¬ p2027))
    (h10719 : p2027 ∨ (¬ p2685) ∨ (¬ p3246) ∨ (¬ p3297) ∨ (¬ p4035) ∨ (¬ p4280) ∨ (¬ p5295))
    : (¬ p2685) ∨ (¬ p3246) ∨ (¬ p3297) ∨ (¬ p4035) ∨ (¬ p4280) ∨ (¬ p5295) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2685 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3297 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4035 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4280 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10719 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41761 (p2027 p2311 p2891 p3246 p3821 p4198 p4522 : Prop)
    (h40810 : (¬ p2027))
    (h10720 : p2027 ∨ (¬ p2311) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3821) ∨ (¬ p4198) ∨ (¬ p4522))
    : (¬ p2311) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3821) ∨ (¬ p4198) ∨ (¬ p4522) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2311 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4522 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10720 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41763 (p2027 p2619 p3544 p3554 p3969 p4875 p5693 : Prop)
    (h40810 : (¬ p2027))
    (h10722 : p2027 ∨ (¬ p2619) ∨ (¬ p3544) ∨ (¬ p3554) ∨ (¬ p3969) ∨ (¬ p4875) ∨ (¬ p5693))
    : (¬ p2619) ∨ (¬ p3544) ∨ (¬ p3554) ∨ (¬ p3969) ∨ (¬ p4875) ∨ (¬ p5693) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3544 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3554 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10722 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41764 (p2027 p2619 p3146 p3661 p4118 p5053 : Prop)
    (h40810 : (¬ p2027))
    (h10723 : p2027 ∨ (¬ p2619) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p5053))
    : (¬ p2619) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p5053) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10723 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41765 (p2027 p2751 p2891 p2957 p3556 p4315 p4365 : Prop)
    (h40810 : (¬ p2027))
    (h10724 : p2027 ∨ (¬ p2751) ∨ (¬ p2891) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p4315) ∨ (¬ p4365))
    : (¬ p2751) ∨ (¬ p2891) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p4315) ∨ (¬ p4365) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2751 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10724 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41767 (p2027 p2145 p2177 p2651 p2685 p2810 p3570 p3646 p4117 p4204 p4570 : Prop)
    (h40810 : (¬ p2027))
    (h10726 : p2027 ∨ (¬ p2145) ∨ (¬ p2177) ∨ (¬ p2651) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p3570) ∨ (¬ p3646) ∨ (¬ p4117) ∨ (¬ p4204) ∨ (¬ p4570))
    : (¬ p2145) ∨ (¬ p2177) ∨ (¬ p2651) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p3570) ∨ (¬ p3646) ∨ (¬ p4117) ∨ (¬ p4204) ∨ (¬ p4570) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2145 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h10726 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step41768 (p2027 p2881 p2933 p3544 p3941 p4277 p5693 : Prop)
    (h40810 : (¬ p2027))
    (h10727 : p2027 ∨ (¬ p2881) ∨ (¬ p2933) ∨ (¬ p3544) ∨ (¬ p3941) ∨ (¬ p4277) ∨ (¬ p5693))
    : (¬ p2881) ∨ (¬ p2933) ∨ (¬ p3544) ∨ (¬ p3941) ∨ (¬ p4277) ∨ (¬ p5693) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2933 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3544 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10727 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41769 (p2027 p3097 p3737 p4276 p5475 p5503 : Prop)
    (h40810 : (¬ p2027))
    (h10728 : p2027 ∨ (¬ p3097) ∨ (¬ p3737) ∨ (¬ p4276) ∨ (¬ p5475) ∨ (¬ p5503))
    : (¬ p3097) ∨ (¬ p3737) ∨ (¬ p4276) ∨ (¬ p5475) ∨ (¬ p5503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3097 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10728 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41772 (p2027 p2387 p2619 p3758 p4441 p4486 : Prop)
    (h40810 : (¬ p2027))
    (h10731 : p2027 ∨ (¬ p2387) ∨ (¬ p2619) ∨ (¬ p3758) ∨ (¬ p4441) ∨ (¬ p4486))
    : (¬ p2387) ∨ (¬ p2619) ∨ (¬ p3758) ∨ (¬ p4441) ∨ (¬ p4486) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2387 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10731 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41777 (p2027 p2210 p2247 p4282 p4360 p5062 : Prop)
    (h40810 : (¬ p2027))
    (h10737 : p2027 ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p4282) ∨ (¬ p4360) ∨ (¬ p5062))
    : (¬ p2210) ∨ (¬ p2247) ∨ (¬ p4282) ∨ (¬ p4360) ∨ (¬ p5062) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5062 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10737 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41779 (p2027 p3347 p3434 p3540 p4278 p5085 p5214 : Prop)
    (h40810 : (¬ p2027))
    (h10739 : p2027 ∨ (¬ p3347) ∨ (¬ p3434) ∨ (¬ p3540) ∨ (¬ p4278) ∨ (¬ p5085) ∨ (¬ p5214))
    : (¬ p3347) ∨ (¬ p3434) ∨ (¬ p3540) ∨ (¬ p4278) ∨ (¬ p5085) ∨ (¬ p5214) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3347 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5085 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5214 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10739 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41780 (p2027 p2145 p2177 p2437 p2630 p2696 p3556 p3570 p4276 : Prop)
    (h40810 : (¬ p2027))
    (h10741 : p2027 ∨ (¬ p2145) ∨ (¬ p2177) ∨ (¬ p2437) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4276))
    : (¬ p2145) ∨ (¬ p2177) ∨ (¬ p2437) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4276) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2145 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h10741 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step41783 (p2027 p2177 p2437 p2481 p3960 p4256 p4276 : Prop)
    (h40810 : (¬ p2027))
    (h10778 : p2027 ∨ (¬ p2177) ∨ (¬ p2437) ∨ (¬ p2481) ∨ (¬ p3960) ∨ (¬ p4256) ∨ (¬ p4276))
    : (¬ p2177) ∨ (¬ p2437) ∨ (¬ p2481) ∨ (¬ p3960) ∨ (¬ p4256) ∨ (¬ p4276) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2481 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10778 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41784 (p2027 p2751 p3038 p3572 p3631 p3821 p4155 : Prop)
    (h40810 : (¬ p2027))
    (h10779 : p2027 ∨ (¬ p2751) ∨ (¬ p3038) ∨ (¬ p3572) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4155))
    : (¬ p2751) ∨ (¬ p3038) ∨ (¬ p3572) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4155) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2751 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3038 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10779 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41786 (p2027 p2311 p2598 p2753 p2850 p3204 p3550 p3551 p3727 p4347 p4444 p4870 p5400 : Prop)
    (h40810 : (¬ p2027))
    (h10781 : p2027 ∨ (¬ p2311) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p2850) ∨ (¬ p3204) ∨ (¬ p3550) ∨ (¬ p3551) ∨ (¬ p3727) ∨ (¬ p4347) ∨ (¬ p4444) ∨ (¬ p4870) ∨ (¬ p5400))
    : (¬ p2311) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p2850) ∨ (¬ p3204) ∨ (¬ p3550) ∨ (¬ p3551) ∨ (¬ p3727) ∨ (¬ p4347) ∨ (¬ p4444) ∨ (¬ p4870) ∨ (¬ p5400) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2311 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p5400 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : (¬ p2027) := h40810;
    (Or.elim h10781 (fun q0 => (False.elim (u12 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (False.elim (r11 u11)))))))))))))))))))))))))))

theorem step41787 (p2027 p2440 p2531 p3083 p5433 p5569 : Prop)
    (h40810 : (¬ p2027))
    (h10782 : p2027 ∨ (¬ p2440) ∨ (¬ p2531) ∨ (¬ p3083) ∨ (¬ p5433) ∨ (¬ p5569))
    : (¬ p2440) ∨ (¬ p2531) ∨ (¬ p3083) ∨ (¬ p5433) ∨ (¬ p5569) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2531 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10782 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41788 (p2027 p2598 p2753 p2850 p2982 p3204 p3266 p3946 p4191 p4450 p4870 : Prop)
    (h40810 : (¬ p2027))
    (h10783 : p2027 ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p3204) ∨ (¬ p3266) ∨ (¬ p3946) ∨ (¬ p4191) ∨ (¬ p4450) ∨ (¬ p4870))
    : (¬ p2598) ∨ (¬ p2753) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p3204) ∨ (¬ p3266) ∨ (¬ p3946) ∨ (¬ p4191) ∨ (¬ p4450) ∨ (¬ p4870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h10783 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step41789 (p2027 p2584 p2589 p2667 p2685 p3579 p4195 p4646 : Prop)
    (h40810 : (¬ p2027))
    (h10784 : p2027 ∨ (¬ p2584) ∨ (¬ p2589) ∨ (¬ p2667) ∨ (¬ p2685) ∨ (¬ p3579) ∨ (¬ p4195) ∨ (¬ p4646))
    : (¬ p2584) ∨ (¬ p2589) ∨ (¬ p2667) ∨ (¬ p2685) ∨ (¬ p3579) ∨ (¬ p4195) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2584 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h10784 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41791 (p2027 p2493 p2589 p3347 p4203 p4948 p5043 : Prop)
    (h40810 : (¬ p2027))
    (h10787 : p2027 ∨ (¬ p2493) ∨ (¬ p2589) ∨ (¬ p3347) ∨ (¬ p4203) ∨ (¬ p4948) ∨ (¬ p5043))
    : (¬ p2493) ∨ (¬ p2589) ∨ (¬ p3347) ∨ (¬ p4203) ∨ (¬ p4948) ∨ (¬ p5043) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10787 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41793 (p2027 p2363 p3266 p4322 p4335 p4433 : Prop)
    (h40810 : (¬ p2027))
    (h10791 : p2027 ∨ (¬ p2363) ∨ (¬ p3266) ∨ (¬ p4322) ∨ (¬ p4335) ∨ (¬ p4433))
    : (¬ p2363) ∨ (¬ p3266) ∨ (¬ p4322) ∨ (¬ p4335) ∨ (¬ p4433) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4335 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10791 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41794 (p2027 p3461 p3692 p3990 p4433 p4444 : Prop)
    (h40810 : (¬ p2027))
    (h10792 : p2027 ∨ (¬ p3461) ∨ (¬ p3692) ∨ (¬ p3990) ∨ (¬ p4433) ∨ (¬ p4444))
    : (¬ p3461) ∨ (¬ p3692) ∨ (¬ p3990) ∨ (¬ p4433) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10792 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41795 (p2027 p2829 p3574 p3585 p4390 p4753 : Prop)
    (h40810 : (¬ p2027))
    (h10793 : p2027 ∨ (¬ p2829) ∨ (¬ p3574) ∨ (¬ p3585) ∨ (¬ p4390) ∨ (¬ p4753))
    : (¬ p2829) ∨ (¬ p3574) ∨ (¬ p3585) ∨ (¬ p4390) ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10793 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41796 (p2027 p2493 p3379 p3555 p4034 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h10794 : p2027 ∨ (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4034) ∨ (¬ p4717))
    : (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4034) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4034 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10794 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41797 (p2027 p3201 p3486 p3569 p3684 p4629 : Prop)
    (h40810 : (¬ p2027))
    (h10795 : p2027 ∨ (¬ p3201) ∨ (¬ p3486) ∨ (¬ p3569) ∨ (¬ p3684) ∨ (¬ p4629))
    : (¬ p3201) ∨ (¬ p3486) ∨ (¬ p3569) ∨ (¬ p3684) ∨ (¬ p4629) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3201 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10795 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41798 (p2027 p2138 p2493 p2598 p3590 p3698 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h10796 : p2027 ∨ (¬ p2138) ∨ (¬ p2493) ∨ (¬ p2598) ∨ (¬ p3590) ∨ (¬ p3698) ∨ (¬ p4717))
    : (¬ p2138) ∨ (¬ p2493) ∨ (¬ p2598) ∨ (¬ p3590) ∨ (¬ p3698) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10796 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41799 (p2027 p2579 p2829 p3585 p4390 p4727 : Prop)
    (h40810 : (¬ p2027))
    (h10797 : p2027 ∨ (¬ p2579) ∨ (¬ p2829) ∨ (¬ p3585) ∨ (¬ p4390) ∨ (¬ p4727))
    : (¬ p2579) ∨ (¬ p2829) ∨ (¬ p3585) ∨ (¬ p4390) ∨ (¬ p4727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10797 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41800 (p2027 p2829 p3585 p3684 p4390 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h10798 : p2027 ∨ (¬ p2829) ∨ (¬ p3585) ∨ (¬ p3684) ∨ (¬ p4390) ∨ (¬ p4717))
    : (¬ p2829) ∨ (¬ p3585) ∨ (¬ p3684) ∨ (¬ p4390) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10798 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41801 (p2027 p2528 p3016 p3878 p4118 p4595 : Prop)
    (h40810 : (¬ p2027))
    (h10799 : p2027 ∨ (¬ p2528) ∨ (¬ p3016) ∨ (¬ p3878) ∨ (¬ p4118) ∨ (¬ p4595))
    : (¬ p2528) ∨ (¬ p3016) ∨ (¬ p3878) ∨ (¬ p4118) ∨ (¬ p4595) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3878 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4595 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10799 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41802 (p2027 p2707 p3585 p3658 p3684 p4646 : Prop)
    (h40810 : (¬ p2027))
    (h10800 : p2027 ∨ (¬ p2707) ∨ (¬ p3585) ∨ (¬ p3658) ∨ (¬ p3684) ∨ (¬ p4646))
    : (¬ p2707) ∨ (¬ p3585) ∨ (¬ p3658) ∨ (¬ p3684) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3658 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10800 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41803 (p2027 p2138 p2774 p4185 p4244 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h10801 : p2027 ∨ (¬ p2138) ∨ (¬ p2774) ∨ (¬ p4185) ∨ (¬ p4244) ∨ (¬ p4555))
    : (¬ p2138) ∨ (¬ p2774) ∨ (¬ p4185) ∨ (¬ p4244) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10801 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41804 (p2027 p2608 p2761 p2839 p3105 p3946 p4191 p4395 p5021 : Prop)
    (h40810 : (¬ p2027))
    (h10802 : p2027 ∨ (¬ p2608) ∨ (¬ p2761) ∨ (¬ p2839) ∨ (¬ p3105) ∨ (¬ p3946) ∨ (¬ p4191) ∨ (¬ p4395) ∨ (¬ p5021))
    : (¬ p2608) ∨ (¬ p2761) ∨ (¬ p2839) ∨ (¬ p3105) ∨ (¬ p3946) ∨ (¬ p4191) ∨ (¬ p4395) ∨ (¬ p5021) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h10802 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step41806 (p2027 p3286 p3414 p4278 p4653 p4660 : Prop)
    (h40810 : (¬ p2027))
    (h10804 : p2027 ∨ (¬ p3286) ∨ (¬ p3414) ∨ (¬ p4278) ∨ (¬ p4653) ∨ (¬ p4660))
    : (¬ p3286) ∨ (¬ p3414) ∨ (¬ p4278) ∨ (¬ p4653) ∨ (¬ p4660) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3286 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4653 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10804 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41808 (p2027 p2810 p3609 p4118 p4373 p5011 : Prop)
    (h40810 : (¬ p2027))
    (h10806 : p2027 ∨ (¬ p2810) ∨ (¬ p3609) ∨ (¬ p4118) ∨ (¬ p4373) ∨ (¬ p5011))
    : (¬ p2810) ∨ (¬ p3609) ∨ (¬ p4118) ∨ (¬ p4373) ∨ (¬ p5011) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2810 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5011 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10806 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41809 (p2027 p2383 p2962 p3556 p3989 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h10807 : p2027 ∨ (¬ p2383) ∨ (¬ p2962) ∨ (¬ p3556) ∨ (¬ p3989) ∨ (¬ p4555))
    : (¬ p2383) ∨ (¬ p2962) ∨ (¬ p3556) ∨ (¬ p3989) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10807 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41811 (p2027 p2761 p3945 p4133 p4347 p4444 : Prop)
    (h40810 : (¬ p2027))
    (h10809 : p2027 ∨ (¬ p2761) ∨ (¬ p3945) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4444))
    : (¬ p2761) ∨ (¬ p3945) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3945 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10809 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41812 (p2027 p2459 p2881 p3955 p4347 p4559 : Prop)
    (h40810 : (¬ p2027))
    (h10810 : p2027 ∨ (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3955) ∨ (¬ p4347) ∨ (¬ p4559))
    : (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3955) ∨ (¬ p4347) ∨ (¬ p4559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10810 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41813 (p2027 p2553 p2881 p3956 p4138 p4559 : Prop)
    (h40810 : (¬ p2027))
    (h10811 : p2027 ∨ (¬ p2553) ∨ (¬ p2881) ∨ (¬ p3956) ∨ (¬ p4138) ∨ (¬ p4559))
    : (¬ p2553) ∨ (¬ p2881) ∨ (¬ p3956) ∨ (¬ p4138) ∨ (¬ p4559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10811 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41814 (p2027 p2881 p3399 p3542 p3860 p4911 : Prop)
    (h40810 : (¬ p2027))
    (h10812 : p2027 ∨ (¬ p2881) ∨ (¬ p3399) ∨ (¬ p3542) ∨ (¬ p3860) ∨ (¬ p4911))
    : (¬ p2881) ∨ (¬ p3399) ∨ (¬ p3542) ∨ (¬ p3860) ∨ (¬ p4911) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10812 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41815 (p2027 p2177 p2295 p3581 p3644 p4976 : Prop)
    (h40810 : (¬ p2027))
    (h10813 : p2027 ∨ (¬ p2177) ∨ (¬ p2295) ∨ (¬ p3581) ∨ (¬ p3644) ∨ (¬ p4976))
    : (¬ p2177) ∨ (¬ p2295) ∨ (¬ p3581) ∨ (¬ p3644) ∨ (¬ p4976) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4976 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10813 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41816 (p2027 p2295 p2579 p2588 p2659 p3019 : Prop)
    (h40810 : (¬ p2027))
    (h10814 : p2027 ∨ (¬ p2295) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2659) ∨ (¬ p3019))
    : (¬ p2295) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2659) ∨ (¬ p3019) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10814 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41817 (p2027 p2252 p2750 p3093 p3319 p3414 p3553 p3954 p4330 p4348 : Prop)
    (h40810 : (¬ p2027))
    (h10815 : p2027 ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3954) ∨ (¬ p4330) ∨ (¬ p4348))
    : (¬ p2252) ∨ (¬ p2750) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3954) ∨ (¬ p4330) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h10815 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step41818 (p2027 p2230 p3238 p3402 p3591 p4079 p4756 : Prop)
    (h40810 : (¬ p2027))
    (h10816 : p2027 ∨ (¬ p2230) ∨ (¬ p3238) ∨ (¬ p3402) ∨ (¬ p3591) ∨ (¬ p4079) ∨ (¬ p4756))
    : (¬ p2230) ∨ (¬ p3238) ∨ (¬ p3402) ∨ (¬ p3591) ∨ (¬ p4079) ∨ (¬ p4756) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4756 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10816 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41821 (p2027 p2797 p3567 p4110 p4315 p4356 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h10819 : p2027 ∨ (¬ p2797) ∨ (¬ p3567) ∨ (¬ p4110) ∨ (¬ p4315) ∨ (¬ p4356) ∨ (¬ p4705))
    : (¬ p2797) ∨ (¬ p3567) ∨ (¬ p4110) ∨ (¬ p4315) ∨ (¬ p4356) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10819 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41823 (p2027 p2881 p2901 p2954 p3551 p4984 : Prop)
    (h40810 : (¬ p2027))
    (h10821 : p2027 ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2954) ∨ (¬ p3551) ∨ (¬ p4984))
    : (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2954) ∨ (¬ p3551) ∨ (¬ p4984) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10821 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41824 (p2027 p3323 p3461 p3746 p4425 p4976 : Prop)
    (h40810 : (¬ p2027))
    (h10822 : p2027 ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3746) ∨ (¬ p4425) ∨ (¬ p4976))
    : (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3746) ∨ (¬ p4425) ∨ (¬ p4976) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3746 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4976 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10822 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41825 (p2027 p2685 p2954 p3556 p4315 p4333 : Prop)
    (h40810 : (¬ p2027))
    (h10823 : p2027 ∨ (¬ p2685) ∨ (¬ p2954) ∨ (¬ p3556) ∨ (¬ p4315) ∨ (¬ p4333))
    : (¬ p2685) ∨ (¬ p2954) ∨ (¬ p3556) ∨ (¬ p4315) ∨ (¬ p4333) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2685 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10823 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41827 (p2027 p2901 p3237 p3680 p4192 p4425 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h10825 : p2027 ∨ (¬ p2901) ∨ (¬ p3237) ∨ (¬ p3680) ∨ (¬ p4192) ∨ (¬ p4425) ∨ (¬ p4705))
    : (¬ p2901) ∨ (¬ p3237) ∨ (¬ p3680) ∨ (¬ p4192) ∨ (¬ p4425) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3237 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10825 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41828 (p2027 p3506 p4322 p4705 p4948 p5038 : Prop)
    (h40810 : (¬ p2027))
    (h10826 : p2027 ∨ (¬ p3506) ∨ (¬ p4322) ∨ (¬ p4705) ∨ (¬ p4948) ∨ (¬ p5038))
    : (¬ p3506) ∨ (¬ p4322) ∨ (¬ p4705) ∨ (¬ p4948) ∨ (¬ p5038) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5038 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10826 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41829 (p2027 p2138 p2774 p4110 p4185 p4885 : Prop)
    (h40810 : (¬ p2027))
    (h10827 : p2027 ∨ (¬ p2138) ∨ (¬ p2774) ∨ (¬ p4110) ∨ (¬ p4185) ∨ (¬ p4885))
    : (¬ p2138) ∨ (¬ p2774) ∨ (¬ p4110) ∨ (¬ p4185) ∨ (¬ p4885) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10827 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41831 (p2027 p2187 p2284 p4275 p4320 p4405 : Prop)
    (h40810 : (¬ p2027))
    (h10829 : p2027 ∨ (¬ p2187) ∨ (¬ p2284) ∨ (¬ p4275) ∨ (¬ p4320) ∨ (¬ p4405))
    : (¬ p2187) ∨ (¬ p2284) ∨ (¬ p4275) ∨ (¬ p4320) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10829 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41832 (p2027 p2109 p2264 p2707 p3960 p4242 p4779 : Prop)
    (h40810 : (¬ p2027))
    (h10830 : p2027 ∨ (¬ p2109) ∨ (¬ p2264) ∨ (¬ p2707) ∨ (¬ p3960) ∨ (¬ p4242) ∨ (¬ p4779))
    : (¬ p2109) ∨ (¬ p2264) ∨ (¬ p2707) ∨ (¬ p3960) ∨ (¬ p4242) ∨ (¬ p4779) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2109 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4779 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10830 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41833 (p2027 p2110 p3055 p3998 p4364 p4749 p5612 : Prop)
    (h40810 : (¬ p2027))
    (h10831 : p2027 ∨ (¬ p2110) ∨ (¬ p3055) ∨ (¬ p3998) ∨ (¬ p4364) ∨ (¬ p4749) ∨ (¬ p5612))
    : (¬ p2110) ∨ (¬ p3055) ∨ (¬ p3998) ∨ (¬ p4364) ∨ (¬ p4749) ∨ (¬ p5612) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2110 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5612 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10831 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41834 (p2027 p2737 p3483 p3953 p4026 p4842 : Prop)
    (h40810 : (¬ p2027))
    (h10832 : p2027 ∨ (¬ p2737) ∨ (¬ p3483) ∨ (¬ p3953) ∨ (¬ p4026) ∨ (¬ p4842))
    : (¬ p2737) ∨ (¬ p3483) ∨ (¬ p3953) ∨ (¬ p4026) ∨ (¬ p4842) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4026 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10832 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41836 (p2027 p3256 p3568 p4341 p4347 p4405 : Prop)
    (h40810 : (¬ p2027))
    (h10835 : p2027 ∨ (¬ p3256) ∨ (¬ p3568) ∨ (¬ p4341) ∨ (¬ p4347) ∨ (¬ p4405))
    : (¬ p3256) ∨ (¬ p3568) ∨ (¬ p4341) ∨ (¬ p4347) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10835 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41837 (p2027 p2274 p3093 p4366 p4427 p4514 : Prop)
    (h40810 : (¬ p2027))
    (h10836 : p2027 ∨ (¬ p2274) ∨ (¬ p3093) ∨ (¬ p4366) ∨ (¬ p4427) ∨ (¬ p4514))
    : (¬ p2274) ∨ (¬ p3093) ∨ (¬ p4366) ∨ (¬ p4427) ∨ (¬ p4514) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10836 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41839 (p2027 p2532 p2534 p3105 p3694 p4158 : Prop)
    (h40810 : (¬ p2027))
    (h10838 : p2027 ∨ (¬ p2532) ∨ (¬ p2534) ∨ (¬ p3105) ∨ (¬ p3694) ∨ (¬ p4158))
    : (¬ p2532) ∨ (¬ p2534) ∨ (¬ p3105) ∨ (¬ p3694) ∨ (¬ p4158) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2532 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4158 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10838 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41840 (p2027 p2252 p2579 p2630 p2655 p2745 p3016 : Prop)
    (h40810 : (¬ p2027))
    (h10839 : p2027 ∨ (¬ p2252) ∨ (¬ p2579) ∨ (¬ p2630) ∨ (¬ p2655) ∨ (¬ p2745) ∨ (¬ p3016))
    : (¬ p2252) ∨ (¬ p2579) ∨ (¬ p2630) ∨ (¬ p2655) ∨ (¬ p2745) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10839 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41841 (p2027 p2579 p2696 p3422 p3905 p4749 : Prop)
    (h40810 : (¬ p2027))
    (h10840 : p2027 ∨ (¬ p2579) ∨ (¬ p2696) ∨ (¬ p3422) ∨ (¬ p3905) ∨ (¬ p4749))
    : (¬ p2579) ∨ (¬ p2696) ∨ (¬ p3422) ∨ (¬ p3905) ∨ (¬ p4749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10840 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41843 (p2027 p2470 p3367 p4242 p4730 p5369 : Prop)
    (h40810 : (¬ p2027))
    (h10842 : p2027 ∨ (¬ p2470) ∨ (¬ p3367) ∨ (¬ p4242) ∨ (¬ p4730) ∨ (¬ p5369))
    : (¬ p2470) ∨ (¬ p3367) ∨ (¬ p4242) ∨ (¬ p4730) ∨ (¬ p5369) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5369 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10842 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41844 (p2027 p2470 p2528 p4340 p4730 p5368 : Prop)
    (h40810 : (¬ p2027))
    (h10843 : p2027 ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p4340) ∨ (¬ p4730) ∨ (¬ p5368))
    : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p4340) ∨ (¬ p4730) ∨ (¬ p5368) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10843 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41845 (p2027 p2589 p2659 p2810 p3136 p4241 : Prop)
    (h40810 : (¬ p2027))
    (h10844 : p2027 ∨ (¬ p2589) ∨ (¬ p2659) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p4241))
    : (¬ p2589) ∨ (¬ p2659) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p4241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10844 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41846 (p2027 p2860 p3367 p4173 p4874 p4881 : Prop)
    (h40810 : (¬ p2027))
    (h10845 : p2027 ∨ (¬ p2860) ∨ (¬ p3367) ∨ (¬ p4173) ∨ (¬ p4874) ∨ (¬ p4881))
    : (¬ p2860) ∨ (¬ p3367) ∨ (¬ p4173) ∨ (¬ p4874) ∨ (¬ p4881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2860 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10845 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41848 (p2027 p2373 p3146 p3661 p4118 p4702 : Prop)
    (h40810 : (¬ p2027))
    (h10847 : p2027 ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p4702))
    : (¬ p2373) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10847 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41849 (p2027 p2088 p3156 p3949 p4208 p4532 : Prop)
    (h40810 : (¬ p2027))
    (h10848 : p2027 ∨ (¬ p2088) ∨ (¬ p3156) ∨ (¬ p3949) ∨ (¬ p4208) ∨ (¬ p4532))
    : (¬ p2088) ∨ (¬ p3156) ∨ (¬ p3949) ∨ (¬ p4208) ∨ (¬ p4532) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3949 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4532 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10848 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41850 (p2027 p3073 p3497 p3692 p4496 p4960 : Prop)
    (h40810 : (¬ p2027))
    (h10849 : p2027 ∨ (¬ p3073) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p4496) ∨ (¬ p4960))
    : (¬ p3073) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p4496) ∨ (¬ p4960) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4496 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10849 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41852 (p2027 p2122 p2177 p2311 p2782 p3551 : Prop)
    (h40810 : (¬ p2027))
    (h10851 : p2027 ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2311) ∨ (¬ p2782) ∨ (¬ p3551))
    : (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2311) ∨ (¬ p2782) ∨ (¬ p3551) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2782 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10851 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41853 (p2027 p2528 p3497 p4261 p4355 p4446 p4702 : Prop)
    (h40810 : (¬ p2027))
    (h10852 : p2027 ∨ (¬ p2528) ∨ (¬ p3497) ∨ (¬ p4261) ∨ (¬ p4355) ∨ (¬ p4446) ∨ (¬ p4702))
    : (¬ p2528) ∨ (¬ p3497) ∨ (¬ p4261) ∨ (¬ p4355) ∨ (¬ p4446) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4446 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10852 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41854 (p2027 p2972 p3680 p4314 p4960 p5284 : Prop)
    (h40810 : (¬ p2027))
    (h10853 : p2027 ∨ (¬ p2972) ∨ (¬ p3680) ∨ (¬ p4314) ∨ (¬ p4960) ∨ (¬ p5284))
    : (¬ p2972) ∨ (¬ p3680) ∨ (¬ p4314) ∨ (¬ p4960) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4314 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10853 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41855 (p2027 p3707 p4208 p4322 p4942 p4960 : Prop)
    (h40810 : (¬ p2027))
    (h10854 : p2027 ∨ (¬ p3707) ∨ (¬ p4208) ∨ (¬ p4322) ∨ (¬ p4942) ∨ (¬ p4960))
    : (¬ p3707) ∨ (¬ p4208) ∨ (¬ p4322) ∨ (¬ p4942) ∨ (¬ p4960) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4942 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10854 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41857 (p2027 p2498 p3319 p3422 p4037 p4194 p4753 : Prop)
    (h40810 : (¬ p2027))
    (h10856 : p2027 ∨ (¬ p2498) ∨ (¬ p3319) ∨ (¬ p3422) ∨ (¬ p4037) ∨ (¬ p4194) ∨ (¬ p4753))
    : (¬ p2498) ∨ (¬ p3319) ∨ (¬ p3422) ∨ (¬ p4037) ∨ (¬ p4194) ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2498 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10856 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41858 (p2027 p2470 p2579 p2588 p4157 p4405 : Prop)
    (h40810 : (¬ p2027))
    (h10857 : p2027 ∨ (¬ p2470) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p4157) ∨ (¬ p4405))
    : (¬ p2470) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p4157) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10857 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41859 (p2027 p2098 p2753 p3688 p3822 p4326 p4405 : Prop)
    (h40810 : (¬ p2027))
    (h10858 : p2027 ∨ (¬ p2098) ∨ (¬ p2753) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p4326) ∨ (¬ p4405))
    : (¬ p2098) ∨ (¬ p2753) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p4326) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4326 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10858 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41861 (p2027 p2241 p2387 p3027 p3931 p4347 p4444 p4826 p5021 : Prop)
    (h40810 : (¬ p2027))
    (h10860 : p2027 ∨ (¬ p2241) ∨ (¬ p2387) ∨ (¬ p3027) ∨ (¬ p3931) ∨ (¬ p4347) ∨ (¬ p4444) ∨ (¬ p4826) ∨ (¬ p5021))
    : (¬ p2241) ∨ (¬ p2387) ∨ (¬ p3027) ∨ (¬ p3931) ∨ (¬ p4347) ∨ (¬ p4444) ∨ (¬ p4826) ∨ (¬ p5021) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h10860 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step41864 (p2027 p2210 p2427 p4366 p4629 p4909 : Prop)
    (h40810 : (¬ p2027))
    (h10863 : p2027 ∨ (¬ p2210) ∨ (¬ p2427) ∨ (¬ p4366) ∨ (¬ p4629) ∨ (¬ p4909))
    : (¬ p2210) ∨ (¬ p2427) ∨ (¬ p4366) ∨ (¬ p4629) ∨ (¬ p4909) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4909 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10863 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41866 (p2027 p2383 p2779 p3917 p3979 p4171 p5122 : Prop)
    (h40810 : (¬ p2027))
    (h10867 : p2027 ∨ (¬ p2383) ∨ (¬ p2779) ∨ (¬ p3917) ∨ (¬ p3979) ∨ (¬ p4171) ∨ (¬ p5122))
    : (¬ p2383) ∨ (¬ p2779) ∨ (¬ p3917) ∨ (¬ p3979) ∨ (¬ p4171) ∨ (¬ p5122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2779 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10867 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41867 (p2027 p2132 p2440 p3055 p4210 p4418 p4753 : Prop)
    (h40810 : (¬ p2027))
    (h10868 : p2027 ∨ (¬ p2132) ∨ (¬ p2440) ∨ (¬ p3055) ∨ (¬ p4210) ∨ (¬ p4418) ∨ (¬ p4753))
    : (¬ p2132) ∨ (¬ p2440) ∨ (¬ p3055) ∨ (¬ p4210) ∨ (¬ p4418) ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10868 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41868 (p2027 p2241 p2727 p3591 p4319 p4972 : Prop)
    (h40810 : (¬ p2027))
    (h10869 : p2027 ∨ (¬ p2241) ∨ (¬ p2727) ∨ (¬ p3591) ∨ (¬ p4319) ∨ (¬ p4972))
    : (¬ p2241) ∨ (¬ p2727) ∨ (¬ p3591) ∨ (¬ p4319) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10869 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41870 (p2027 p2936 p3449 p3644 p4366 p5307 : Prop)
    (h40810 : (¬ p2027))
    (h10871 : p2027 ∨ (¬ p2936) ∨ (¬ p3449) ∨ (¬ p3644) ∨ (¬ p4366) ∨ (¬ p5307))
    : (¬ p2936) ∨ (¬ p3449) ∨ (¬ p3644) ∨ (¬ p4366) ∨ (¬ p5307) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2936 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10871 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41872 (p2027 p2619 p3644 p4244 p4277 p4312 p4378 : Prop)
    (h40810 : (¬ p2027))
    (h10873 : p2027 ∨ (¬ p2619) ∨ (¬ p3644) ∨ (¬ p4244) ∨ (¬ p4277) ∨ (¬ p4312) ∨ (¬ p4378))
    : (¬ p2619) ∨ (¬ p3644) ∨ (¬ p4244) ∨ (¬ p4277) ∨ (¬ p4312) ∨ (¬ p4378) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4378 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10873 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41873 (p2027 p2470 p3146 p3346 p4158 p4440 : Prop)
    (h40810 : (¬ p2027))
    (h10874 : p2027 ∨ (¬ p2470) ∨ (¬ p3146) ∨ (¬ p3346) ∨ (¬ p4158) ∨ (¬ p4440))
    : (¬ p2470) ∨ (¬ p3146) ∨ (¬ p3346) ∨ (¬ p4158) ∨ (¬ p4440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4158 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10874 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41874 (p2027 p2476 p2534 p2659 p3256 p4121 : Prop)
    (h40810 : (¬ p2027))
    (h10875 : p2027 ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2659) ∨ (¬ p3256) ∨ (¬ p4121))
    : (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2659) ∨ (¬ p3256) ∨ (¬ p4121) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2476 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4121 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10875 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41876 (p2027 p2881 p3309 p3923 p3960 p4113 p4559 : Prop)
    (h40810 : (¬ p2027))
    (h10877 : p2027 ∨ (¬ p2881) ∨ (¬ p3309) ∨ (¬ p3923) ∨ (¬ p3960) ∨ (¬ p4113) ∨ (¬ p4559))
    : (¬ p2881) ∨ (¬ p3309) ∨ (¬ p3923) ∨ (¬ p3960) ∨ (¬ p4113) ∨ (¬ p4559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4113 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10877 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41877 (p2027 p2307 p2387 p2881 p4138 p4559 : Prop)
    (h40810 : (¬ p2027))
    (h10878 : p2027 ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2881) ∨ (¬ p4138) ∨ (¬ p4559))
    : (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2881) ∨ (¬ p4138) ∨ (¬ p4559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10878 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41878 (p2027 p2088 p2482 p2656 p2992 p4261 p4262 p4704 : Prop)
    (h40810 : (¬ p2027))
    (h10879 : p2027 ∨ (¬ p2088) ∨ (¬ p2482) ∨ (¬ p2656) ∨ (¬ p2992) ∨ (¬ p4261) ∨ (¬ p4262) ∨ (¬ p4704))
    : (¬ p2088) ∨ (¬ p2482) ∨ (¬ p2656) ∨ (¬ p2992) ∨ (¬ p4261) ∨ (¬ p4262) ∨ (¬ p4704) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2482 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4262 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4704 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h10879 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41880 (p2027 p2241 p2685 p2745 p3032 p4366 : Prop)
    (h40810 : (¬ p2027))
    (h10881 : p2027 ∨ (¬ p2241) ∨ (¬ p2685) ∨ (¬ p2745) ∨ (¬ p3032) ∨ (¬ p4366))
    : (¬ p2241) ∨ (¬ p2685) ∨ (¬ p2745) ∨ (¬ p3032) ∨ (¬ p4366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10881 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41881 (p2027 p2299 p3115 p4042 p4320 p4335 p4559 : Prop)
    (h40810 : (¬ p2027))
    (h10882 : p2027 ∨ (¬ p2299) ∨ (¬ p3115) ∨ (¬ p4042) ∨ (¬ p4320) ∨ (¬ p4335) ∨ (¬ p4559))
    : (¬ p2299) ∨ (¬ p3115) ∨ (¬ p4042) ∨ (¬ p4320) ∨ (¬ p4335) ∨ (¬ p4559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4335 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10882 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41882 (p2027 p2192 p2608 p3369 p3646 p4377 : Prop)
    (h40810 : (¬ p2027))
    (h10883 : p2027 ∨ (¬ p2192) ∨ (¬ p2608) ∨ (¬ p3369) ∨ (¬ p3646) ∨ (¬ p4377))
    : (¬ p2192) ∨ (¬ p2608) ∨ (¬ p3369) ∨ (¬ p3646) ∨ (¬ p4377) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3369 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10883 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41883 (p2027 p2589 p2659 p2901 p3413 p4235 : Prop)
    (h40810 : (¬ p2027))
    (h10884 : p2027 ∨ (¬ p2589) ∨ (¬ p2659) ∨ (¬ p2901) ∨ (¬ p3413) ∨ (¬ p4235))
    : (¬ p2589) ∨ (¬ p2659) ∨ (¬ p2901) ∨ (¬ p3413) ∨ (¬ p4235) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10884 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41884 (p2027 p2319 p2727 p3031 p3516 p3567 p3817 p4972 : Prop)
    (h40810 : (¬ p2027))
    (h10885 : p2027 ∨ (¬ p2319) ∨ (¬ p2727) ∨ (¬ p3031) ∨ (¬ p3516) ∨ (¬ p3567) ∨ (¬ p3817) ∨ (¬ p4972))
    : (¬ p2319) ∨ (¬ p2727) ∨ (¬ p3031) ∨ (¬ p3516) ∨ (¬ p3567) ∨ (¬ p3817) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h10885 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41885 (p2027 p2449 p2651 p3821 p4650 p4849 : Prop)
    (h40810 : (¬ p2027))
    (h10886 : p2027 ∨ (¬ p2449) ∨ (¬ p2651) ∨ (¬ p3821) ∨ (¬ p4650) ∨ (¬ p4849))
    : (¬ p2449) ∨ (¬ p2651) ∨ (¬ p3821) ∨ (¬ p4650) ∨ (¬ p4849) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4849 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10886 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41886 (p2027 p2307 p2727 p3549 p3567 p4245 p4972 : Prop)
    (h40810 : (¬ p2027))
    (h10887 : p2027 ∨ (¬ p2307) ∨ (¬ p2727) ∨ (¬ p3549) ∨ (¬ p3567) ∨ (¬ p4245) ∨ (¬ p4972))
    : (¬ p2307) ∨ (¬ p2727) ∨ (¬ p3549) ∨ (¬ p3567) ∨ (¬ p4245) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10887 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41888 (p2027 p2373 p2542 p3742 p4001 p4904 : Prop)
    (h40810 : (¬ p2027))
    (h10889 : p2027 ∨ (¬ p2373) ∨ (¬ p2542) ∨ (¬ p3742) ∨ (¬ p4001) ∨ (¬ p4904))
    : (¬ p2373) ∨ (¬ p2542) ∨ (¬ p3742) ∨ (¬ p4001) ∨ (¬ p4904) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10889 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41889 (p2027 p2651 p2963 p3422 p4389 p4753 : Prop)
    (h40810 : (¬ p2027))
    (h10890 : p2027 ∨ (¬ p2651) ∨ (¬ p2963) ∨ (¬ p3422) ∨ (¬ p4389) ∨ (¬ p4753))
    : (¬ p2651) ∨ (¬ p2963) ∨ (¬ p3422) ∨ (¬ p4389) ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10890 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41890 (p2027 p2264 p3146 p3947 p4445 p4905 : Prop)
    (h40810 : (¬ p2027))
    (h10891 : p2027 ∨ (¬ p2264) ∨ (¬ p3146) ∨ (¬ p3947) ∨ (¬ p4445) ∨ (¬ p4905))
    : (¬ p2264) ∨ (¬ p3146) ∨ (¬ p3947) ∨ (¬ p4445) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10891 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41891 (p2027 p2498 p3016 p3379 p3591 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h10892 : p2027 ∨ (¬ p2498) ∨ (¬ p3016) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p4811))
    : (¬ p2498) ∨ (¬ p3016) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2498 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10892 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41892 (p2027 p2307 p2578 p3016 p3549 p4202 p4512 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h10893 : p2027 ∨ (¬ p2307) ∨ (¬ p2578) ∨ (¬ p3016) ∨ (¬ p3549) ∨ (¬ p4202) ∨ (¬ p4512) ∨ (¬ p4811))
    : (¬ p2307) ∨ (¬ p2578) ∨ (¬ p3016) ∨ (¬ p3549) ∨ (¬ p4202) ∨ (¬ p4512) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h10893 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41893 (p2027 p2177 p2307 p2459 p2781 p3365 p4208 p4315 p5059 : Prop)
    (h40810 : (¬ p2027))
    (h10895 : p2027 ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2459) ∨ (¬ p2781) ∨ (¬ p3365) ∨ (¬ p4208) ∨ (¬ p4315) ∨ (¬ p5059))
    : (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2459) ∨ (¬ p2781) ∨ (¬ p3365) ∨ (¬ p4208) ∨ (¬ p4315) ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h10895 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step41897 (p2027 p2579 p2662 p2745 p3422 p3475 p4111 : Prop)
    (h40810 : (¬ p2027))
    (h10899 : p2027 ∨ (¬ p2579) ∨ (¬ p2662) ∨ (¬ p2745) ∨ (¬ p3422) ∨ (¬ p3475) ∨ (¬ p4111))
    : (¬ p2579) ∨ (¬ p2662) ∨ (¬ p2745) ∨ (¬ p3422) ∨ (¬ p3475) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10899 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41898 (p2027 p2668 p3093 p3922 p4275 p4366 p4405 p4909 : Prop)
    (h40810 : (¬ p2027))
    (h10900 : p2027 ∨ (¬ p2668) ∨ (¬ p3093) ∨ (¬ p3922) ∨ (¬ p4275) ∨ (¬ p4366) ∨ (¬ p4405) ∨ (¬ p4909))
    : (¬ p2668) ∨ (¬ p3093) ∨ (¬ p3922) ∨ (¬ p4275) ∨ (¬ p4366) ∨ (¬ p4405) ∨ (¬ p4909) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4909 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h10900 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41901 (p2027 p2246 p2331 p2668 p2751 p4358 p4841 : Prop)
    (h40810 : (¬ p2027))
    (h10903 : p2027 ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p2751) ∨ (¬ p4358) ∨ (¬ p4841))
    : (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p2751) ∨ (¬ p4358) ∨ (¬ p4841) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4841 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10903 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41904 (p2027 p2579 p3389 p4710 p5472 p5514 : Prop)
    (h40810 : (¬ p2027))
    (h10907 : p2027 ∨ (¬ p2579) ∨ (¬ p3389) ∨ (¬ p4710) ∨ (¬ p5472) ∨ (¬ p5514))
    : (¬ p2579) ∨ (¬ p3389) ∨ (¬ p4710) ∨ (¬ p5472) ∨ (¬ p5514) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5472 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10907 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41906 (p2027 p3527 p3551 p3585 p3687 p3959 p5086 : Prop)
    (h40810 : (¬ p2027))
    (h10909 : p2027 ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p3585) ∨ (¬ p3687) ∨ (¬ p3959) ∨ (¬ p5086))
    : (¬ p3527) ∨ (¬ p3551) ∨ (¬ p3585) ∨ (¬ p3687) ∨ (¬ p3959) ∨ (¬ p5086) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3687 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5086 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10909 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41907 (p2027 p2807 p3246 p3292 p4280 p4656 : Prop)
    (h40810 : (¬ p2027))
    (h10910 : p2027 ∨ (¬ p2807) ∨ (¬ p3246) ∨ (¬ p3292) ∨ (¬ p4280) ∨ (¬ p4656))
    : (¬ p2807) ∨ (¬ p3246) ∨ (¬ p3292) ∨ (¬ p4280) ∨ (¬ p4656) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2807 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3292 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4280 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10910 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41909 (p2027 p2264 p2427 p4031 p4120 p4132 p4362 : Prop)
    (h40810 : (¬ p2027))
    (h10912 : p2027 ∨ (¬ p2264) ∨ (¬ p2427) ∨ (¬ p4031) ∨ (¬ p4120) ∨ (¬ p4132) ∨ (¬ p4362))
    : (¬ p2264) ∨ (¬ p2427) ∨ (¬ p4031) ∨ (¬ p4120) ∨ (¬ p4132) ∨ (¬ p4362) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10912 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41911 (p2027 p3644 p3998 p4590 p5203 p5558 : Prop)
    (h40810 : (¬ p2027))
    (h10914 : p2027 ∨ (¬ p3644) ∨ (¬ p3998) ∨ (¬ p4590) ∨ (¬ p5203) ∨ (¬ p5558))
    : (¬ p3644) ∨ (¬ p3998) ∨ (¬ p4590) ∨ (¬ p5203) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3644 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10914 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41912 (p2027 p2441 p2449 p3580 p4256 p4278 p4608 : Prop)
    (h40810 : (¬ p2027))
    (h10915 : p2027 ∨ (¬ p2441) ∨ (¬ p2449) ∨ (¬ p3580) ∨ (¬ p4256) ∨ (¬ p4278) ∨ (¬ p4608))
    : (¬ p2441) ∨ (¬ p2449) ∨ (¬ p3580) ∨ (¬ p4256) ∨ (¬ p4278) ∨ (¬ p4608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2441 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10915 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41913 (p2027 p3527 p3551 p3959 p4235 p4344 p4431 p4632 : Prop)
    (h40810 : (¬ p2027))
    (h10916 : p2027 ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p3959) ∨ (¬ p4235) ∨ (¬ p4344) ∨ (¬ p4431) ∨ (¬ p4632))
    : (¬ p3527) ∨ (¬ p3551) ∨ (¬ p3959) ∨ (¬ p4235) ∨ (¬ p4344) ∨ (¬ p4431) ∨ (¬ p4632) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h10916 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41914 (p2027 p2230 p2870 p2933 p3540 p4885 p4909 : Prop)
    (h40810 : (¬ p2027))
    (h10917 : p2027 ∨ (¬ p2230) ∨ (¬ p2870) ∨ (¬ p2933) ∨ (¬ p3540) ∨ (¬ p4885) ∨ (¬ p4909))
    : (¬ p2230) ∨ (¬ p2870) ∨ (¬ p2933) ∨ (¬ p3540) ∨ (¬ p4885) ∨ (¬ p4909) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2933 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4909 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10917 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41915 (p2027 p2751 p3707 p4035 p4759 p5153 p5284 : Prop)
    (h40810 : (¬ p2027))
    (h10918 : p2027 ∨ (¬ p2751) ∨ (¬ p3707) ∨ (¬ p4035) ∨ (¬ p4759) ∨ (¬ p5153) ∨ (¬ p5284))
    : (¬ p2751) ∨ (¬ p3707) ∨ (¬ p4035) ∨ (¬ p4759) ∨ (¬ p5153) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2751 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4035 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10918 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41916 (p2027 p2579 p3389 p3822 p4710 p5222 : Prop)
    (h40810 : (¬ p2027))
    (h10919 : p2027 ∨ (¬ p2579) ∨ (¬ p3389) ∨ (¬ p3822) ∨ (¬ p4710) ∨ (¬ p5222))
    : (¬ p2579) ∨ (¬ p3389) ∨ (¬ p3822) ∨ (¬ p4710) ∨ (¬ p5222) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10919 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41917 (p2027 p2177 p3969 p4260 p4905 p5557 : Prop)
    (h40810 : (¬ p2027))
    (h10920 : p2027 ∨ (¬ p2177) ∨ (¬ p3969) ∨ (¬ p4260) ∨ (¬ p4905) ∨ (¬ p5557))
    : (¬ p2177) ∨ (¬ p3969) ∨ (¬ p4260) ∨ (¬ p4905) ∨ (¬ p5557) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5557 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10920 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41921 (p2027 p2230 p3115 p3346 p4705 p4947 : Prop)
    (h40810 : (¬ p2027))
    (h10926 : p2027 ∨ (¬ p2230) ∨ (¬ p3115) ∨ (¬ p3346) ∨ (¬ p4705) ∨ (¬ p4947))
    : (¬ p2230) ∨ (¬ p3115) ∨ (¬ p3346) ∨ (¬ p4705) ∨ (¬ p4947) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10926 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41922 (p2027 p2952 p3166 p4311 p4320 p4904 : Prop)
    (h40810 : (¬ p2027))
    (h10927 : p2027 ∨ (¬ p2952) ∨ (¬ p3166) ∨ (¬ p4311) ∨ (¬ p4320) ∨ (¬ p4904))
    : (¬ p2952) ∨ (¬ p3166) ∨ (¬ p4311) ∨ (¬ p4320) ∨ (¬ p4904) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2952 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10927 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41923 (p2027 p2191 p2220 p2542 p4109 p4202 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h10928 : p2027 ∨ (¬ p2191) ∨ (¬ p2220) ∨ (¬ p2542) ∨ (¬ p4109) ∨ (¬ p4202) ∨ (¬ p4811))
    : (¬ p2191) ∨ (¬ p2220) ∨ (¬ p2542) ∨ (¬ p4109) ∨ (¬ p4202) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10928 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41924 (p2027 p2579 p2655 p2807 p3016 p4652 : Prop)
    (h40810 : (¬ p2027))
    (h10929 : p2027 ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2807) ∨ (¬ p3016) ∨ (¬ p4652))
    : (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2807) ∨ (¬ p3016) ∨ (¬ p4652) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10929 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41925 (p2027 p2122 p2177 p2252 p2589 p2655 p2750 p2829 p3146 p4118 p4346 p4607 p4905 : Prop)
    (h40810 : (¬ p2027))
    (h10931 : p2027 ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2252) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p2829) ∨ (¬ p3146) ∨ (¬ p4118) ∨ (¬ p4346) ∨ (¬ p4607) ∨ (¬ p4905))
    : (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2252) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p2829) ∨ (¬ p3146) ∨ (¬ p4118) ∨ (¬ p4346) ∨ (¬ p4607) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4607 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : (¬ p2027) := h40810;
    (Or.elim h10931 (fun q0 => (False.elim (u12 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (False.elim (r11 u11)))))))))))))))))))))))))))

theorem step41927 (p2027 p2518 p2563 p4173 p4202 p4610 : Prop)
    (h40810 : (¬ p2027))
    (h10934 : p2027 ∨ (¬ p2518) ∨ (¬ p2563) ∨ (¬ p4173) ∨ (¬ p4202) ∨ (¬ p4610))
    : (¬ p2518) ∨ (¬ p2563) ∨ (¬ p4173) ∨ (¬ p4202) ∨ (¬ p4610) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4610 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10934 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41929 (p2027 p2406 p2589 p2662 p4154 p4281 p4972 : Prop)
    (h40810 : (¬ p2027))
    (h10936 : p2027 ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2662) ∨ (¬ p4154) ∨ (¬ p4281) ∨ (¬ p4972))
    : (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2662) ∨ (¬ p4154) ∨ (¬ p4281) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10936 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41930 (p2027 p2241 p2745 p3136 p3412 p3555 : Prop)
    (h40810 : (¬ p2027))
    (h10937 : p2027 ∨ (¬ p2241) ∨ (¬ p2745) ∨ (¬ p3136) ∨ (¬ p3412) ∨ (¬ p3555))
    : (¬ p2241) ∨ (¬ p2745) ∨ (¬ p3136) ∨ (¬ p3412) ∨ (¬ p3555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10937 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41931 (p2027 p3136 p3745 p4195 p4272 p5449 : Prop)
    (h40810 : (¬ p2027))
    (h10938 : p2027 ∨ (¬ p3136) ∨ (¬ p3745) ∨ (¬ p4195) ∨ (¬ p4272) ∨ (¬ p5449))
    : (¬ p3136) ∨ (¬ p3745) ∨ (¬ p4195) ∨ (¬ p4272) ∨ (¬ p5449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4272 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10938 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41932 (p2027 p2363 p2383 p2781 p3055 p3266 p3684 p5405 p5433 : Prop)
    (h40810 : (¬ p2027))
    (h10939 : p2027 ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3055) ∨ (¬ p3266) ∨ (¬ p3684) ∨ (¬ p5405) ∨ (¬ p5433))
    : (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3055) ∨ (¬ p3266) ∨ (¬ p3684) ∨ (¬ p5405) ∨ (¬ p5433) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h10939 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step41933 (p2027 p2498 p3379 p3422 p3591 p5214 : Prop)
    (h40810 : (¬ p2027))
    (h10940 : p2027 ∨ (¬ p2498) ∨ (¬ p3379) ∨ (¬ p3422) ∨ (¬ p3591) ∨ (¬ p5214))
    : (¬ p2498) ∨ (¬ p3379) ∨ (¬ p3422) ∨ (¬ p3591) ∨ (¬ p5214) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2498 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5214 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10940 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41934 (p2027 p2850 p3096 p3584 p3727 p5449 : Prop)
    (h40810 : (¬ p2027))
    (h10941 : p2027 ∨ (¬ p2850) ∨ (¬ p3096) ∨ (¬ p3584) ∨ (¬ p3727) ∨ (¬ p5449))
    : (¬ p2850) ∨ (¬ p3096) ∨ (¬ p3584) ∨ (¬ p3727) ∨ (¬ p5449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10941 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41935 (p2027 p2307 p2396 p2761 p2781 p3365 p4315 p5405 p5740 : Prop)
    (h40810 : (¬ p2027))
    (h10942 : p2027 ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p2781) ∨ (¬ p3365) ∨ (¬ p4315) ∨ (¬ p5405) ∨ (¬ p5740))
    : (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p2781) ∨ (¬ p3365) ∨ (¬ p4315) ∨ (¬ p5405) ∨ (¬ p5740) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h10942 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step41936 (p2027 p2383 p2781 p3055 p3461 p3684 p3990 p4444 p4948 p5059 : Prop)
    (h40810 : (¬ p2027))
    (h10943 : p2027 ∨ (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3055) ∨ (¬ p3461) ∨ (¬ p3684) ∨ (¬ p3990) ∨ (¬ p4444) ∨ (¬ p4948) ∨ (¬ p5059))
    : (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3055) ∨ (¬ p3461) ∨ (¬ p3684) ∨ (¬ p3990) ∨ (¬ p4444) ∨ (¬ p4948) ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h10943 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step41938 (p2027 p2850 p3379 p3555 p4034 p5214 : Prop)
    (h40810 : (¬ p2027))
    (h10945 : p2027 ∨ (¬ p2850) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4034) ∨ (¬ p5214))
    : (¬ p2850) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4034) ∨ (¬ p5214) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4034 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5214 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10945 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41940 (p2027 p2406 p2901 p2928 p4001 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h10947 : p2027 ∨ (¬ p2406) ∨ (¬ p2901) ∨ (¬ p2928) ∨ (¬ p4001) ∨ (¬ p4705))
    : (¬ p2406) ∨ (¬ p2901) ∨ (¬ p2928) ∨ (¬ p4001) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10947 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41941 (p2027 p2210 p2563 p3591 p3957 p4629 : Prop)
    (h40810 : (¬ p2027))
    (h10949 : p2027 ∨ (¬ p2210) ∨ (¬ p2563) ∨ (¬ p3591) ∨ (¬ p3957) ∨ (¬ p4629))
    : (¬ p2210) ∨ (¬ p2563) ∨ (¬ p3591) ∨ (¬ p3957) ∨ (¬ p4629) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10949 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41942 (p2027 p2284 p2307 p3549 p3743 p4512 p4957 : Prop)
    (h40810 : (¬ p2027))
    (h10950 : p2027 ∨ (¬ p2284) ∨ (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3743) ∨ (¬ p4512) ∨ (¬ p4957))
    : (¬ p2284) ∨ (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3743) ∨ (¬ p4512) ∨ (¬ p4957) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10950 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41943 (p2027 p2138 p2774 p3952 p4185 p5053 : Prop)
    (h40810 : (¬ p2027))
    (h10951 : p2027 ∨ (¬ p2138) ∨ (¬ p2774) ∨ (¬ p3952) ∨ (¬ p4185) ∨ (¬ p5053))
    : (¬ p2138) ∨ (¬ p2774) ∨ (¬ p3952) ∨ (¬ p4185) ∨ (¬ p5053) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10951 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41944 (p2027 p2553 p2573 p3822 p4730 p5220 : Prop)
    (h40810 : (¬ p2027))
    (h10952 : p2027 ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3822) ∨ (¬ p4730) ∨ (¬ p5220))
    : (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3822) ∨ (¬ p4730) ∨ (¬ p5220) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10952 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41945 (p2027 p3367 p3389 p3688 p3689 p4106 p4730 : Prop)
    (h40810 : (¬ p2027))
    (h10953 : p2027 ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3688) ∨ (¬ p3689) ∨ (¬ p4106) ∨ (¬ p4730))
    : (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3688) ∨ (¬ p3689) ∨ (¬ p4106) ∨ (¬ p4730) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3689 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4106 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10953 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41948 (p2027 p2743 p3361 p3367 p3414 p3683 p4650 : Prop)
    (h40810 : (¬ p2027))
    (h10956 : p2027 ∨ (¬ p2743) ∨ (¬ p3361) ∨ (¬ p3367) ∨ (¬ p3414) ∨ (¬ p3683) ∨ (¬ p4650))
    : (¬ p2743) ∨ (¬ p3361) ∨ (¬ p3367) ∨ (¬ p3414) ∨ (¬ p3683) ∨ (¬ p4650) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2743 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10956 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41949 (p2027 p2717 p3551 p3587 p4283 p4320 p5053 : Prop)
    (h40810 : (¬ p2027))
    (h10957 : p2027 ∨ (¬ p2717) ∨ (¬ p3551) ∨ (¬ p3587) ∨ (¬ p4283) ∨ (¬ p4320) ∨ (¬ p5053))
    : (¬ p2717) ∨ (¬ p3551) ∨ (¬ p3587) ∨ (¬ p4283) ∨ (¬ p4320) ∨ (¬ p5053) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3587 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10957 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41950 (p2027 p2098 p2299 p3425 p4477 p4804 : Prop)
    (h40810 : (¬ p2027))
    (h10958 : p2027 ∨ (¬ p2098) ∨ (¬ p2299) ∨ (¬ p3425) ∨ (¬ p4477) ∨ (¬ p4804))
    : (¬ p2098) ∨ (¬ p2299) ∨ (¬ p3425) ∨ (¬ p4477) ∨ (¬ p4804) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2299 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4804 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10958 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41951 (p2027 p2299 p2319 p2341 p4026 p4620 p5016 : Prop)
    (h40810 : (¬ p2027))
    (h10959 : p2027 ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p4026) ∨ (¬ p4620) ∨ (¬ p5016))
    : (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p4026) ∨ (¬ p4620) ∨ (¬ p5016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4026 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10959 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41952 (p2027 p3497 p3741 p3875 p4149 p4702 p5568 : Prop)
    (h40810 : (¬ p2027))
    (h10960 : p2027 ∨ (¬ p3497) ∨ (¬ p3741) ∨ (¬ p3875) ∨ (¬ p4149) ∨ (¬ p4702) ∨ (¬ p5568))
    : (¬ p3497) ∨ (¬ p3741) ∨ (¬ p3875) ∨ (¬ p4149) ∨ (¬ p4702) ∨ (¬ p5568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3497 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4149 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10960 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41953 (p2027 p2911 p3570 p3741 p4204 p4948 p5043 : Prop)
    (h40810 : (¬ p2027))
    (h10961 : p2027 ∨ (¬ p2911) ∨ (¬ p3570) ∨ (¬ p3741) ∨ (¬ p4204) ∨ (¬ p4948) ∨ (¬ p5043))
    : (¬ p2911) ∨ (¬ p3570) ∨ (¬ p3741) ∨ (¬ p4204) ∨ (¬ p4948) ∨ (¬ p5043) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10961 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41955 (p2027 p2743 p3073 p4340 p4968 p5316 : Prop)
    (h40810 : (¬ p2027))
    (h10963 : p2027 ∨ (¬ p2743) ∨ (¬ p3073) ∨ (¬ p4340) ∨ (¬ p4968) ∨ (¬ p5316))
    : (¬ p2743) ∨ (¬ p3073) ∨ (¬ p4340) ∨ (¬ p4968) ∨ (¬ p5316) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2743 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4968 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10963 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41956 (p2027 p3097 p3631 p4107 p4452 p4518 : Prop)
    (h40810 : (¬ p2027))
    (h10965 : p2027 ∨ (¬ p3097) ∨ (¬ p3631) ∨ (¬ p4107) ∨ (¬ p4452) ∨ (¬ p4518))
    : (¬ p3097) ∨ (¬ p3631) ∨ (¬ p4107) ∨ (¬ p4452) ∨ (¬ p4518) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3097 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10965 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41957 (p2027 p2247 p3662 p3952 p4356 p5017 : Prop)
    (h40810 : (¬ p2027))
    (h10966 : p2027 ∨ (¬ p2247) ∨ (¬ p3662) ∨ (¬ p3952) ∨ (¬ p4356) ∨ (¬ p5017))
    : (¬ p2247) ∨ (¬ p3662) ∨ (¬ p3952) ∨ (¬ p4356) ∨ (¬ p5017) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5017 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10966 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41958 (p2027 p2307 p3791 p3923 p4138 p5016 p5564 : Prop)
    (h40810 : (¬ p2027))
    (h10967 : p2027 ∨ (¬ p2307) ∨ (¬ p3791) ∨ (¬ p3923) ∨ (¬ p4138) ∨ (¬ p5016) ∨ (¬ p5564))
    : (¬ p2307) ∨ (¬ p3791) ∨ (¬ p3923) ∨ (¬ p4138) ∨ (¬ p5016) ∨ (¬ p5564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10967 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41959 (p2027 p2972 p4154 p4208 p4365 p4700 p4972 : Prop)
    (h40810 : (¬ p2027))
    (h10969 : p2027 ∨ (¬ p2972) ∨ (¬ p4154) ∨ (¬ p4208) ∨ (¬ p4365) ∨ (¬ p4700) ∨ (¬ p4972))
    : (¬ p2972) ∨ (¬ p4154) ∨ (¬ p4208) ∨ (¬ p4365) ∨ (¬ p4700) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10969 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41960 (p2027 p2952 p3166 p3694 p4311 p4906 : Prop)
    (h40810 : (¬ p2027))
    (h10970 : p2027 ∨ (¬ p2952) ∨ (¬ p3166) ∨ (¬ p3694) ∨ (¬ p4311) ∨ (¬ p4906))
    : (¬ p2952) ∨ (¬ p3166) ∨ (¬ p3694) ∨ (¬ p4311) ∨ (¬ p4906) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2952 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10970 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41961 (p2027 p3599 p3688 p3744 p4401 p5269 : Prop)
    (h40810 : (¬ p2027))
    (h10971 : p2027 ∨ (¬ p3599) ∨ (¬ p3688) ∨ (¬ p3744) ∨ (¬ p4401) ∨ (¬ p5269))
    : (¬ p3599) ∨ (¬ p3688) ∨ (¬ p3744) ∨ (¬ p4401) ∨ (¬ p5269) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3599 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4401 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5269 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10971 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41965 (p2027 p2737 p2780 p3471 p4400 p4424 p4842 : Prop)
    (h40810 : (¬ p2027))
    (h10975 : p2027 ∨ (¬ p2737) ∨ (¬ p2780) ∨ (¬ p3471) ∨ (¬ p4400) ∨ (¬ p4424) ∨ (¬ p4842))
    : (¬ p2737) ∨ (¬ p2780) ∨ (¬ p3471) ∨ (¬ p4400) ∨ (¬ p4424) ∨ (¬ p4842) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4400 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4424 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10975 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41966 (p2027 p2137 p2307 p2737 p2962 p3549 p3953 p5049 : Prop)
    (h40810 : (¬ p2027))
    (h10976 : p2027 ∨ (¬ p2137) ∨ (¬ p2307) ∨ (¬ p2737) ∨ (¬ p2962) ∨ (¬ p3549) ∨ (¬ p3953) ∨ (¬ p5049))
    : (¬ p2137) ∨ (¬ p2307) ∨ (¬ p2737) ∨ (¬ p2962) ∨ (¬ p3549) ∨ (¬ p3953) ∨ (¬ p5049) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2137 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5049 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h10976 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41967 (p2027 p3367 p4379 p4425 p5159 p5391 p5682 : Prop)
    (h40810 : (¬ p2027))
    (h10977 : p2027 ∨ (¬ p3367) ∨ (¬ p4379) ∨ (¬ p4425) ∨ (¬ p5159) ∨ (¬ p5391) ∨ (¬ p5682))
    : (¬ p3367) ∨ (¬ p4379) ∨ (¬ p4425) ∨ (¬ p5159) ∨ (¬ p5391) ∨ (¬ p5682) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5159 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5682 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10977 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41968 (p2027 p2307 p2497 p2542 p2962 p3549 p4109 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h10978 : p2027 ∨ (¬ p2307) ∨ (¬ p2497) ∨ (¬ p2542) ∨ (¬ p2962) ∨ (¬ p3549) ∨ (¬ p4109) ∨ (¬ p4811))
    : (¬ p2307) ∨ (¬ p2497) ∨ (¬ p2542) ∨ (¬ p2962) ∨ (¬ p3549) ∨ (¬ p4109) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h10978 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41969 (p2027 p2192 p2553 p3096 p4033 p4363 p4620 : Prop)
    (h40810 : (¬ p2027))
    (h10979 : p2027 ∨ (¬ p2192) ∨ (¬ p2553) ∨ (¬ p3096) ∨ (¬ p4033) ∨ (¬ p4363) ∨ (¬ p4620))
    : (¬ p2192) ∨ (¬ p2553) ∨ (¬ p3096) ∨ (¬ p4033) ∨ (¬ p4363) ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4033 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10979 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41970 (p2027 p2476 p2659 p4009 p4121 p4286 : Prop)
    (h40810 : (¬ p2027))
    (h10980 : p2027 ∨ (¬ p2476) ∨ (¬ p2659) ∨ (¬ p4009) ∨ (¬ p4121) ∨ (¬ p4286))
    : (¬ p2476) ∨ (¬ p2659) ∨ (¬ p4009) ∨ (¬ p4121) ∨ (¬ p4286) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2476 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4009 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4121 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10980 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41971 (p2027 p3083 p3359 p4149 p4440 p5122 : Prop)
    (h40810 : (¬ p2027))
    (h10981 : p2027 ∨ (¬ p3083) ∨ (¬ p3359) ∨ (¬ p4149) ∨ (¬ p4440) ∨ (¬ p5122))
    : (¬ p3083) ∨ (¬ p3359) ∨ (¬ p4149) ∨ (¬ p4440) ∨ (¬ p5122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3083 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4149 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10981 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41972 (p2027 p3276 p3744 p4191 p4422 p4718 : Prop)
    (h40810 : (¬ p2027))
    (h10982 : p2027 ∨ (¬ p3276) ∨ (¬ p3744) ∨ (¬ p4191) ∨ (¬ p4422) ∨ (¬ p4718))
    : (¬ p3276) ∨ (¬ p3744) ∨ (¬ p4191) ∨ (¬ p4422) ∨ (¬ p4718) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10982 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41974 (p2027 p2417 p2493 p2926 p3741 p3817 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h10984 : p2027 ∨ (¬ p2417) ∨ (¬ p2493) ∨ (¬ p2926) ∨ (¬ p3741) ∨ (¬ p3817) ∨ (¬ p4717))
    : (¬ p2417) ∨ (¬ p2493) ∨ (¬ p2926) ∨ (¬ p3741) ∨ (¬ p3817) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2926 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10984 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41975 (p2027 p2313 p2553 p3073 p3449 p3692 p3956 p4433 p5021 : Prop)
    (h40810 : (¬ p2027))
    (h10985 : p2027 ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3692) ∨ (¬ p3956) ∨ (¬ p4433) ∨ (¬ p5021))
    : (¬ p2313) ∨ (¬ p2553) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3692) ∨ (¬ p3956) ∨ (¬ p4433) ∨ (¬ p5021) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h10985 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step41976 (p2027 p2459 p3579 p3868 p3919 p4118 p5564 : Prop)
    (h40810 : (¬ p2027))
    (h10986 : p2027 ∨ (¬ p2459) ∨ (¬ p3579) ∨ (¬ p3868) ∨ (¬ p3919) ∨ (¬ p4118) ∨ (¬ p5564))
    : (¬ p2459) ∨ (¬ p3579) ∨ (¬ p3868) ∨ (¬ p3919) ∨ (¬ p4118) ∨ (¬ p5564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10986 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41977 (p2027 p2187 p3093 p3365 p3366 p3555 p3568 p4195 p4377 p4405 p4516 : Prop)
    (h40810 : (¬ p2027))
    (h10988 : p2027 ∨ (¬ p2187) ∨ (¬ p3093) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3555) ∨ (¬ p3568) ∨ (¬ p4195) ∨ (¬ p4377) ∨ (¬ p4405) ∨ (¬ p4516))
    : (¬ p2187) ∨ (¬ p3093) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3555) ∨ (¬ p3568) ∨ (¬ p4195) ∨ (¬ p4377) ∨ (¬ p4405) ∨ (¬ p4516) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h10988 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step41978 (p2027 p3365 p3366 p3399 p3555 p3631 p3877 p3950 p4118 p4377 : Prop)
    (h40810 : (¬ p2027))
    (h10989 : p2027 ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p3631) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4377))
    : (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p3631) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4377) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3365 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h10989 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step41979 (p2027 p2156 p3125 p3365 p3366 p3370 p3461 p3877 p4377 p5123 p5600 : Prop)
    (h40810 : (¬ p2027))
    (h10990 : p2027 ∨ (¬ p2156) ∨ (¬ p3125) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3461) ∨ (¬ p3877) ∨ (¬ p4377) ∨ (¬ p5123) ∨ (¬ p5600))
    : (¬ p2156) ∨ (¬ p3125) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3461) ∨ (¬ p3877) ∨ (¬ p4377) ∨ (¬ p5123) ∨ (¬ p5600) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h10990 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step41980 (p2027 p3641 p4149 p4440 p5122 p5160 : Prop)
    (h40810 : (¬ p2027))
    (h10991 : p2027 ∨ (¬ p3641) ∨ (¬ p4149) ∨ (¬ p4440) ∨ (¬ p5122) ∨ (¬ p5160))
    : (¬ p3641) ∨ (¬ p4149) ∨ (¬ p4440) ∨ (¬ p5122) ∨ (¬ p5160) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4149 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10991 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41981 (p2027 p2139 p2761 p3051 p3246 p3365 p3877 p5123 p5600 : Prop)
    (h40810 : (¬ p2027))
    (h10992 : p2027 ∨ (¬ p2139) ∨ (¬ p2761) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p5123) ∨ (¬ p5600))
    : (¬ p2139) ∨ (¬ p2761) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p5123) ∨ (¬ p5600) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2139 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h10992 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step41982 (p2027 p2139 p2156 p2274 p2396 p3365 p3877 p3950 p4118 : Prop)
    (h40810 : (¬ p2027))
    (h10993 : p2027 ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118))
    : (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2139 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h10993 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step41983 (p2027 p2307 p2962 p3097 p3125 p3365 p3366 p3370 p3877 p3950 p4118 p4377 p4623 : Prop)
    (h40810 : (¬ p2027))
    (h10994 : p2027 ∨ (¬ p2307) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4377) ∨ (¬ p4623))
    : (¬ p2307) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4377) ∨ (¬ p4623) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4623 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : (¬ p2027) := h40810;
    (Or.elim h10994 (fun q0 => (False.elim (u12 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u10))) (fun r11 => (False.elim (r11 u11)))))))))))))))))))))))))))

theorem step41984 (p2027 p2138 p2696 p2839 p3585 p4749 : Prop)
    (h40810 : (¬ p2027))
    (h10995 : p2027 ∨ (¬ p2138) ∨ (¬ p2696) ∨ (¬ p2839) ∨ (¬ p3585) ∨ (¬ p4749))
    : (¬ p2138) ∨ (¬ p2696) ∨ (¬ p2839) ∨ (¬ p3585) ∨ (¬ p4749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10995 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41985 (p2027 p2493 p3051 p3486 p4109 p4202 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h10996 : p2027 ∨ (¬ p2493) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p4109) ∨ (¬ p4202) ∨ (¬ p4717))
    : (¬ p2493) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p4109) ∨ (¬ p4202) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10996 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41986 (p2027 p2475 p2518 p3574 p3989 p4113 p4116 p4718 : Prop)
    (h40810 : (¬ p2027))
    (h10997 : p2027 ∨ (¬ p2475) ∨ (¬ p2518) ∨ (¬ p3574) ∨ (¬ p3989) ∨ (¬ p4113) ∨ (¬ p4116) ∨ (¬ p4718))
    : (¬ p2475) ∨ (¬ p2518) ∨ (¬ p3574) ∨ (¬ p3989) ∨ (¬ p4113) ∨ (¬ p4116) ∨ (¬ p4718) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2475 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4113 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h10997 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41987 (p2027 p2143 p2829 p3556 p3583 p4185 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h10998 : p2027 ∨ (¬ p2143) ∨ (¬ p2829) ∨ (¬ p3556) ∨ (¬ p3583) ∨ (¬ p4185) ∨ (¬ p4555))
    : (¬ p2143) ∨ (¬ p2829) ∨ (¬ p3556) ∨ (¬ p3583) ∨ (¬ p4185) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10998 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41988 (p2027 p3093 p3483 p3834 p4867 p5148 : Prop)
    (h40810 : (¬ p2027))
    (h10999 : p2027 ∨ (¬ p3093) ∨ (¬ p3483) ∨ (¬ p3834) ∨ (¬ p4867) ∨ (¬ p5148))
    : (¬ p3093) ∨ (¬ p3483) ∨ (¬ p3834) ∨ (¬ p4867) ∨ (¬ p5148) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3093 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3834 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4867 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5148 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10999 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41990 (p2027 p2166 p2481 p2542 p3696 p4256 p4632 : Prop)
    (h40810 : (¬ p2027))
    (h11001 : p2027 ∨ (¬ p2166) ∨ (¬ p2481) ∨ (¬ p2542) ∨ (¬ p3696) ∨ (¬ p4256) ∨ (¬ p4632))
    : (¬ p2166) ∨ (¬ p2481) ∨ (¬ p2542) ∨ (¬ p3696) ∨ (¬ p4256) ∨ (¬ p4632) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2481 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h11001 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41992 (p2027 p2470 p2579 p3989 p4157 p4718 : Prop)
    (h40810 : (¬ p2027))
    (h11003 : p2027 ∨ (¬ p2470) ∨ (¬ p2579) ∨ (¬ p3989) ∨ (¬ p4157) ∨ (¬ p4718))
    : (¬ p2470) ∨ (¬ p2579) ∨ (¬ p3989) ∨ (¬ p4157) ∨ (¬ p4718) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11003 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41993 (p2027 p2187 p2247 p2307 p3097 p4111 p4256 p4384 p5017 : Prop)
    (h40810 : (¬ p2027))
    (h11004 : p2027 ∨ (¬ p2187) ∨ (¬ p2247) ∨ (¬ p2307) ∨ (¬ p3097) ∨ (¬ p4111) ∨ (¬ p4256) ∨ (¬ p4384) ∨ (¬ p5017))
    : (¬ p2187) ∨ (¬ p2247) ∨ (¬ p2307) ∨ (¬ p3097) ∨ (¬ p4111) ∨ (¬ p4256) ∨ (¬ p4384) ∨ (¬ p5017) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4384 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5017 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h11004 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step41994 (p2027 p2247 p2307 p2459 p2881 p3359 p4111 p4275 p4697 p5017 : Prop)
    (h40810 : (¬ p2027))
    (h11005 : p2027 ∨ (¬ p2247) ∨ (¬ p2307) ∨ (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3359) ∨ (¬ p4111) ∨ (¬ p4275) ∨ (¬ p4697) ∨ (¬ p5017))
    : (¬ p2247) ∨ (¬ p2307) ∨ (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3359) ∨ (¬ p4111) ∨ (¬ p4275) ∨ (¬ p4697) ∨ (¬ p5017) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5017 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h11005 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step41995 (p2027 p3551 p3641 p3876 p4404 p5199 : Prop)
    (h40810 : (¬ p2027))
    (h11006 : p2027 ∨ (¬ p3551) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p4404) ∨ (¬ p5199))
    : (¬ p3551) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p4404) ∨ (¬ p5199) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3551 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4404 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5199 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11006 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41999 (p2027 p3256 p3692 p3880 p4237 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h11010 : p2027 ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4237) ∨ (¬ p4705))
    : (¬ p3256) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4237) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4237 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11010 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42000 (p2027 p2247 p3449 p4111 p4288 p5011 : Prop)
    (h40810 : (¬ p2027))
    (h11011 : p2027 ∨ (¬ p2247) ∨ (¬ p3449) ∨ (¬ p4111) ∨ (¬ p4288) ∨ (¬ p5011))
    : (¬ p2247) ∨ (¬ p3449) ∨ (¬ p4111) ∨ (¬ p4288) ∨ (¬ p5011) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4288 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5011 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11011 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42001 (p2027 p2247 p2751 p3037 p3399 p3572 : Prop)
    (h40810 : (¬ p2027))
    (h11012 : p2027 ∨ (¬ p2247) ∨ (¬ p2751) ∨ (¬ p3037) ∨ (¬ p3399) ∨ (¬ p3572))
    : (¬ p2247) ∨ (¬ p2751) ∨ (¬ p3037) ∨ (¬ p3399) ∨ (¬ p3572) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11012 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42002 (p2027 p3830 p3860 p4347 p4352 p4998 : Prop)
    (h40810 : (¬ p2027))
    (h11013 : p2027 ∨ (¬ p3830) ∨ (¬ p3860) ∨ (¬ p4347) ∨ (¬ p4352) ∨ (¬ p4998))
    : (¬ p3830) ∨ (¬ p3860) ∨ (¬ p4347) ∨ (¬ p4352) ∨ (¬ p4998) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3830 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11013 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42003 (p2027 p3399 p3591 p4427 p4435 p5472 : Prop)
    (h40810 : (¬ p2027))
    (h11014 : p2027 ∨ (¬ p3399) ∨ (¬ p3591) ∨ p4427 ∨ (¬ p4435) ∨ (¬ p5472))
    : (¬ p3399) ∨ (¬ p3591) ∨ p4427 ∨ (¬ p4435) ∨ (¬ p5472) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p4427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5472 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11014 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u2 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42004 (p2027 p3246 p3399 p3834 p4911 p5358 : Prop)
    (h40810 : (¬ p2027))
    (h11015 : p2027 ∨ (¬ p3246) ∨ (¬ p3399) ∨ (¬ p3834) ∨ (¬ p4911) ∨ (¬ p5358))
    : (¬ p3246) ∨ (¬ p3399) ∨ (¬ p3834) ∨ (¬ p4911) ∨ (¬ p5358) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3834 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11015 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42005 (p2027 p2982 p3440 p3680 p4321 p4492 p4629 : Prop)
    (h40810 : (¬ p2027))
    (h11016 : p2027 ∨ (¬ p2982) ∨ (¬ p3440) ∨ (¬ p3680) ∨ (¬ p4321) ∨ (¬ p4492) ∨ (¬ p4629))
    : (¬ p2982) ∨ (¬ p3440) ∨ (¬ p3680) ∨ (¬ p4321) ∨ (¬ p4492) ∨ (¬ p4629) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4321 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4492 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h11016 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step42006 (p2027 p2187 p2192 p3486 p4275 p4405 : Prop)
    (h40810 : (¬ p2027))
    (h11017 : p2027 ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p3486) ∨ (¬ p4275) ∨ (¬ p4405))
    : (¬ p2187) ∨ (¬ p2192) ∨ (¬ p3486) ∨ (¬ p4275) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11017 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42007 (p2027 p3549 p3707 p4349 p4405 p4417 p5153 p5284 : Prop)
    (h40810 : (¬ p2027))
    (h11018 : p2027 ∨ (¬ p3549) ∨ (¬ p3707) ∨ (¬ p4349) ∨ (¬ p4405) ∨ (¬ p4417) ∨ (¬ p5153) ∨ (¬ p5284))
    : (¬ p3549) ∨ (¬ p3707) ∨ (¬ p4349) ∨ (¬ p4405) ∨ (¬ p4417) ∨ (¬ p5153) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3549 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4349 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h11018 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step42009 (p2027 p2860 p3246 p4136 p4324 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h11021 : p2027 ∨ (¬ p2860) ∨ (¬ p3246) ∨ (¬ p4136) ∨ (¬ p4324) ∨ (¬ p4555))
    : (¬ p2860) ∨ (¬ p3246) ∨ (¬ p4136) ∨ (¬ p4324) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2860 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11021 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42010 (p2027 p2542 p3276 p4949 p5170 p5284 : Prop)
    (h40810 : (¬ p2027))
    (h11022 : p2027 ∨ (¬ p2542) ∨ (¬ p3276) ∨ (¬ p4949) ∨ (¬ p5170) ∨ (¬ p5284))
    : (¬ p2542) ∨ (¬ p3276) ∨ (¬ p4949) ∨ (¬ p5170) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4949 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11022 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42011 (p2027 p2534 p2608 p2753 p2774 p3551 p3914 p4404 p4444 p5210 p5250 : Prop)
    (h40810 : (¬ p2027))
    (h11024 : p2027 ∨ (¬ p2534) ∨ (¬ p2608) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3551) ∨ (¬ p3914) ∨ (¬ p4404) ∨ (¬ p4444) ∨ (¬ p5210) ∨ (¬ p5250))
    : (¬ p2534) ∨ (¬ p2608) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3551) ∨ (¬ p3914) ∨ (¬ p4404) ∨ (¬ p4444) ∨ (¬ p5210) ∨ (¬ p5250) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2534 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3914 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4404 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h11024 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step42013 (p2027 p2459 p2881 p3051 p3585 p3954 p4521 p4697 p5160 : Prop)
    (h40810 : (¬ p2027))
    (h11026 : p2027 ∨ (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3585) ∨ (¬ p3954) ∨ (¬ p4521) ∨ (¬ p4697) ∨ (¬ p5160))
    : (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3585) ∨ (¬ p3954) ∨ (¬ p4521) ∨ (¬ p4697) ∨ (¬ p5160) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h11026 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step42014 (p2027 p2187 p2307 p2962 p3097 p3585 p3874 p3954 p4384 p4521 : Prop)
    (h40810 : (¬ p2027))
    (h11027 : p2027 ∨ (¬ p2187) ∨ (¬ p2307) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p3585) ∨ (¬ p3874) ∨ (¬ p3954) ∨ (¬ p4384) ∨ (¬ p4521))
    : (¬ p2187) ∨ (¬ p2307) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p3585) ∨ (¬ p3874) ∨ (¬ p3954) ∨ (¬ p4384) ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4384 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h11027 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step42017 (p2027 p2190 p3744 p3955 p3969 p4620 p5580 : Prop)
    (h40810 : (¬ p2027))
    (h11030 : p2027 ∨ (¬ p2190) ∨ (¬ p3744) ∨ (¬ p3955) ∨ (¬ p3969) ∨ (¬ p4620) ∨ (¬ p5580))
    : (¬ p2190) ∨ (¬ p3744) ∨ (¬ p3955) ∨ (¬ p3969) ∨ (¬ p4620) ∨ (¬ p5580) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2190 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h11030 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step42018 (p2027 p2459 p2668 p3917 p4133 p4171 p4328 : Prop)
    (h40810 : (¬ p2027))
    (h11031 : p2027 ∨ (¬ p2459) ∨ (¬ p2668) ∨ (¬ p3917) ∨ (¬ p4133) ∨ (¬ p4171) ∨ (¬ p4328))
    : (¬ p2459) ∨ (¬ p2668) ∨ (¬ p3917) ∨ (¬ p4133) ∨ (¬ p4171) ∨ (¬ p4328) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h11031 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step42019 (p2027 p2295 p3093 p3834 p3922 p4620 p5148 : Prop)
    (h40810 : (¬ p2027))
    (h11032 : p2027 ∨ (¬ p2295) ∨ (¬ p3093) ∨ (¬ p3834) ∨ (¬ p3922) ∨ (¬ p4620) ∨ (¬ p5148))
    : (¬ p2295) ∨ (¬ p3093) ∨ (¬ p3834) ∨ (¬ p3922) ∨ (¬ p4620) ∨ (¬ p5148) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3834 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5148 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h11032 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step42020 (p2027 p2307 p2373 p3696 p4033 p4197 p4620 p4948 : Prop)
    (h40810 : (¬ p2027))
    (h11033 : p2027 ∨ (¬ p2307) ∨ (¬ p2373) ∨ (¬ p3696) ∨ (¬ p4033) ∨ (¬ p4197) ∨ (¬ p4620) ∨ (¬ p4948))
    : (¬ p2307) ∨ (¬ p2373) ∨ (¬ p3696) ∨ (¬ p4033) ∨ (¬ p4197) ∨ (¬ p4620) ∨ (¬ p4948) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4033 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h11033 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step42021 (p2027 p2145 p2696 p3506 p3556 p3570 p3755 p5123 p5558 : Prop)
    (h40810 : (¬ p2027))
    (h11034 : p2027 ∨ (¬ p2145) ∨ (¬ p2696) ∨ (¬ p3506) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3755) ∨ (¬ p5123) ∨ (¬ p5558))
    : (¬ p2145) ∨ (¬ p2696) ∨ (¬ p3506) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3755) ∨ (¬ p5123) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2145 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h11034 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step42024 (p2027 p2307 p2786 p3365 p3822 p4845 : Prop)
    (h40810 : (¬ p2027))
    (h11038 : p2027 ∨ (¬ p2307) ∨ (¬ p2786) ∨ (¬ p3365) ∨ (¬ p3822) ∨ (¬ p4845))
    : (¬ p2307) ∨ (¬ p2786) ∨ (¬ p3365) ∨ (¬ p3822) ∨ (¬ p4845) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4845 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11038 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42025 (p2027 p2110 p3365 p3998 p4968 p5612 : Prop)
    (h40810 : (¬ p2027))
    (h11039 : p2027 ∨ (¬ p2110) ∨ (¬ p3365) ∨ (¬ p3998) ∨ (¬ p4968) ∨ (¬ p5612))
    : (¬ p2110) ∨ (¬ p3365) ∨ (¬ p3998) ∨ (¬ p4968) ∨ (¬ p5612) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2110 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4968 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5612 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11039 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42026 (p2027 p3365 p3527 p3546 p3659 p3819 p4782 : Prop)
    (h40810 : (¬ p2027))
    (h11040 : p2027 ∨ (¬ p3365) ∨ (¬ p3527) ∨ (¬ p3546) ∨ (¬ p3659) ∨ (¬ p3819) ∨ (¬ p4782))
    : (¬ p3365) ∨ (¬ p3527) ∨ (¬ p3546) ∨ (¬ p3659) ∨ (¬ p3819) ∨ (¬ p4782) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3365 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3546 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4782 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h11040 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step42028 (p2027 p2383 p2786 p3365 p4358 p4845 : Prop)
    (h40810 : (¬ p2027))
    (h11043 : p2027 ∨ (¬ p2383) ∨ (¬ p2786) ∨ (¬ p3365) ∨ (¬ p4358) ∨ (¬ p4845))
    : (¬ p2383) ∨ (¬ p2786) ∨ (¬ p3365) ∨ (¬ p4358) ∨ (¬ p4845) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4845 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11043 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42029 (p2027 p2177 p3192 p3644 p3947 p4451 p4570 : Prop)
    (h40810 : (¬ p2027))
    (h11045 : p2027 ∨ (¬ p2177) ∨ (¬ p3192) ∨ (¬ p3644) ∨ (¬ p3947) ∨ (¬ p4451) ∨ (¬ p4570))
    : (¬ p2177) ∨ (¬ p3192) ∨ (¬ p3644) ∨ (¬ p3947) ∨ (¬ p4451) ∨ (¬ p4570) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4451 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h11045 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step42030 (p2027 p2922 p3379 p3555 p4034 p4646 : Prop)
    (h40810 : (¬ p2027))
    (h11046 : p2027 ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4034) ∨ (¬ p4646))
    : (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4034) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4034 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11046 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42031 (p2027 p3399 p3547 p3591 p4026 p4620 : Prop)
    (h40810 : (¬ p2027))
    (h11047 : p2027 ∨ (¬ p3399) ∨ (¬ p3547) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4620))
    : (¬ p3399) ∨ (¬ p3547) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3547 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4026 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11047 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42032 (p2027 p2470 p3540 p4278 p4404 p4666 : Prop)
    (h40810 : (¬ p2027))
    (h11048 : p2027 ∨ (¬ p2470) ∨ (¬ p3540) ∨ (¬ p4278) ∨ (¬ p4404) ∨ (¬ p4666))
    : (¬ p2470) ∨ (¬ p3540) ∨ (¬ p4278) ∨ (¬ p4404) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4404 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11048 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42034 (p2027 p2406 p2589 p2655 p3361 p3541 p3688 p4842 : Prop)
    (h40810 : (¬ p2027))
    (h11050 : p2027 ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p3361) ∨ (¬ p3541) ∨ (¬ p3688) ∨ (¬ p4842))
    : (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p3361) ∨ (¬ p3541) ∨ (¬ p3688) ∨ (¬ p4842) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h11050 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step42035 (p2027 p2996 p3189 p3570 p4362 p4804 p4963 : Prop)
    (h40810 : (¬ p2027))
    (h11051 : p2027 ∨ (¬ p2996) ∨ (¬ p3189) ∨ (¬ p3570) ∨ (¬ p4362) ∨ (¬ p4804) ∨ (¬ p4963))
    : (¬ p2996) ∨ (¬ p3189) ∨ (¬ p3570) ∨ (¬ p4362) ∨ (¬ p4804) ∨ (¬ p4963) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4804 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h11051 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step42036 (p2027 p2579 p2641 p2659 p3984 p4111 : Prop)
    (h40810 : (¬ p2027))
    (h11052 : p2027 ∨ (¬ p2579) ∨ (¬ p2641) ∨ (¬ p2659) ∨ (¬ p3984) ∨ (¬ p4111))
    : (¬ p2579) ∨ (¬ p2641) ∨ (¬ p2659) ∨ (¬ p3984) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11052 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42037 (p2027 p2531 p3189 p3662 p3988 p4320 p4346 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h11053 : p2027 ∨ (¬ p2531) ∨ (¬ p3189) ∨ (¬ p3662) ∨ (¬ p3988) ∨ (¬ p4320) ∨ (¬ p4346) ∨ (¬ p4555))
    : (¬ p2531) ∨ (¬ p3189) ∨ (¬ p3662) ∨ (¬ p3988) ∨ (¬ p4320) ∨ (¬ p4346) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2531 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h11053 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step42038 (p2027 p3323 p3946 p4110 p4336 p4356 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h11054 : p2027 ∨ (¬ p3323) ∨ (¬ p3946) ∨ (¬ p4110) ∨ (¬ p4336) ∨ (¬ p4356) ∨ (¬ p4705))
    : (¬ p3323) ∨ (¬ p3946) ∨ (¬ p4110) ∨ (¬ p4336) ∨ (¬ p4356) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h11054 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step42039 (p2027 p2641 p3567 p3662 p4110 p4356 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h11055 : p2027 ∨ (¬ p2641) ∨ (¬ p3567) ∨ (¬ p3662) ∨ (¬ p4110) ∨ (¬ p4356) ∨ (¬ p4705))
    : (¬ p2641) ∨ (¬ p3567) ∨ (¬ p3662) ∨ (¬ p4110) ∨ (¬ p4356) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h11055 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step42040 (p2027 p2331 p2952 p3986 p4110 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h11056 : p2027 ∨ (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3986) ∨ (¬ p4110) ∨ (¬ p4705))
    : (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3986) ∨ (¬ p4110) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11056 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42041 (p2027 p3189 p3662 p3919 p4066 p4235 p4283 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h11057 : p2027 ∨ (¬ p3189) ∨ (¬ p3662) ∨ (¬ p3919) ∨ (¬ p4066) ∨ (¬ p4235) ∨ (¬ p4283) ∨ (¬ p4705))
    : (¬ p3189) ∨ (¬ p3662) ∨ (¬ p3919) ∨ (¬ p4066) ∨ (¬ p4235) ∨ (¬ p4283) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h11057 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step42043 (p2027 p2264 p2311 p2995 p3551 p4110 p4356 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h11059 : p2027 ∨ (¬ p2264) ∨ (¬ p2311) ∨ (¬ p2995) ∨ (¬ p3551) ∨ (¬ p4110) ∨ (¬ p4356) ∨ (¬ p4705))
    : (¬ p2264) ∨ (¬ p2311) ∨ (¬ p2995) ∨ (¬ p3551) ∨ (¬ p4110) ∨ (¬ p4356) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h11059 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step42044 (p2027 p2737 p2807 p2811 p3585 p4343 p4652 : Prop)
    (h40810 : (¬ p2027))
    (h11060 : p2027 ∨ (¬ p2737) ∨ (¬ p2807) ∨ (¬ p2811) ∨ (¬ p3585) ∨ (¬ p4343) ∨ (¬ p4652))
    : (¬ p2737) ∨ (¬ p2807) ∨ (¬ p2811) ∨ (¬ p3585) ∨ (¬ p4343) ∨ (¬ p4652) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h11060 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step42046 (p2027 p2313 p2386 p2505 p3238 p3309 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h11063 : p2027 ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p2505) ∨ (¬ p3238) ∨ (¬ p3309) ∨ (¬ p4717))
    : (¬ p2313) ∨ (¬ p2386) ∨ (¬ p2505) ∨ (¬ p3238) ∨ (¬ p3309) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h11063 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step42047 (p2027 p2136 p2860 p3471 p3556 p4136 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h11064 : p2027 ∨ (¬ p2136) ∨ (¬ p2860) ∨ (¬ p3471) ∨ (¬ p3556) ∨ (¬ p4136) ∨ (¬ p4555))
    : (¬ p2136) ∨ (¬ p2860) ∨ (¬ p3471) ∨ (¬ p3556) ∨ (¬ p4136) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h11064 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step42048 (p2027 p2177 p2247 p2553 p2573 p3497 p3662 p4905 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h11065 : p2027 ∨ (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p4905) ∨ (¬ p5190))
    : (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p4905) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h11065 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step42049 (p2027 p2476 p2507 p2573 p3063 p4432 : Prop)
    (h40810 : (¬ p2027))
    (h11066 : p2027 ∨ (¬ p2476) ∨ (¬ p2507) ∨ (¬ p2573) ∨ (¬ p3063) ∨ (¬ p4432))
    : (¬ p2476) ∨ (¬ p2507) ∨ (¬ p2573) ∨ (¬ p3063) ∨ (¬ p4432) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2476 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2507 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11066 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42050 (p2027 p2230 p2247 p3662 p3879 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h11067 : p2027 ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p3662) ∨ (¬ p3879) ∨ (¬ p5190))
    : (¬ p2230) ∨ (¬ p2247) ∨ (¬ p3662) ∨ (¬ p3879) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11067 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42052 (p2027 p2363 p2534 p2668 p3573 p4976 : Prop)
    (h40810 : (¬ p2027))
    (h11070 : p2027 ∨ (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2668) ∨ (¬ p3573) ∨ (¬ p4976))
    : (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2668) ∨ (¬ p3573) ∨ (¬ p4976) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4976 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11070 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42053 (p2027 p2387 p2668 p4110 p4336 p4356 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h11071 : p2027 ∨ (¬ p2387) ∨ (¬ p2668) ∨ (¬ p4110) ∨ (¬ p4336) ∨ (¬ p4356) ∨ (¬ p4705))
    : (¬ p2387) ∨ (¬ p2668) ∨ (¬ p4110) ∨ (¬ p4336) ∨ (¬ p4356) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2387 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h11071 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step42054 (p2027 p2383 p3136 p3567 p4358 p4563 p4841 : Prop)
    (h40810 : (¬ p2027))
    (h11072 : p2027 ∨ (¬ p2383) ∨ (¬ p3136) ∨ (¬ p3567) ∨ (¬ p4358) ∨ (¬ p4563) ∨ (¬ p4841))
    : (¬ p2383) ∨ (¬ p3136) ∨ (¬ p3567) ∨ (¬ p4358) ∨ (¬ p4563) ∨ (¬ p4841) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4841 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h11072 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step42055 (p2027 p2284 p3063 p3957 p4193 p4358 p4906 : Prop)
    (h40810 : (¬ p2027))
    (h11073 : p2027 ∨ (¬ p2284) ∨ (¬ p3063) ∨ (¬ p3957) ∨ (¬ p4193) ∨ (¬ p4358) ∨ (¬ p4906))
    : (¬ p2284) ∨ (¬ p3063) ∨ (¬ p3957) ∨ (¬ p4193) ∨ (¬ p4358) ∨ (¬ p4906) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h11073 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step42058 (p2027 p2122 p2573 p3540 p3921 p5225 : Prop)
    (h40810 : (¬ p2027))
    (h11076 : p2027 ∨ (¬ p2122) ∨ (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3921) ∨ (¬ p5225))
    : (¬ p2122) ∨ (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3921) ∨ (¬ p5225) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5225 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11076 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42059 (p2027 p2717 p3399 p3542 p3860 p4794 : Prop)
    (h40810 : (¬ p2027))
    (h11077 : p2027 ∨ (¬ p2717) ∨ (¬ p3399) ∨ (¬ p3542) ∨ (¬ p3860) ∨ (¬ p4794))
    : (¬ p2717) ∨ (¬ p3399) ∨ (¬ p3542) ∨ (¬ p3860) ∨ (¬ p4794) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4794 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11077 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42060 (p2027 p2630 p2741 p2829 p4111 p4845 : Prop)
    (h40810 : (¬ p2027))
    (h11078 : p2027 ∨ (¬ p2630) ∨ (¬ p2741) ∨ (¬ p2829) ∨ (¬ p4111) ∨ (¬ p4845))
    : (¬ p2630) ∨ (¬ p2741) ∨ (¬ p2829) ∨ (¬ p4111) ∨ (¬ p4845) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4845 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11078 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42061 (p2027 p2122 p2298 p2331 p3414 p4846 : Prop)
    (h40810 : (¬ p2027))
    (h11079 : p2027 ∨ (¬ p2122) ∨ (¬ p2298) ∨ (¬ p2331) ∨ (¬ p3414) ∨ (¬ p4846))
    : (¬ p2122) ∨ (¬ p2298) ∨ (¬ p2331) ∨ (¬ p3414) ∨ (¬ p4846) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2298 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4846 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11079 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42062 (p2027 p2685 p2696 p2753 p3585 p4343 p4652 : Prop)
    (h40810 : (¬ p2027))
    (h11080 : p2027 ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3585) ∨ (¬ p4343) ∨ (¬ p4652))
    : (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3585) ∨ (¬ p4343) ∨ (¬ p4652) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2685 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h11080 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step42063 (p2027 p3027 p3574 p3579 p3660 p4111 p4646 : Prop)
    (h40810 : (¬ p2027))
    (h11081 : p2027 ∨ (¬ p3027) ∨ (¬ p3574) ∨ (¬ p3579) ∨ (¬ p3660) ∨ (¬ p4111) ∨ (¬ p4646))
    : (¬ p3027) ∨ (¬ p3574) ∨ (¬ p3579) ∨ (¬ p3660) ∨ (¬ p4111) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3027 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h11081 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step42064 (p2027 p2220 p2743 p3146 p3877 p3954 p4041 p4348 p4521 : Prop)
    (h40810 : (¬ p2027))
    (h11082 : p2027 ∨ (¬ p2220) ∨ (¬ p2743) ∨ (¬ p3146) ∨ (¬ p3877) ∨ (¬ p3954) ∨ (¬ p4041) ∨ (¬ p4348) ∨ (¬ p4521))
    : (¬ p2220) ∨ (¬ p2743) ∨ (¬ p3146) ∨ (¬ p3877) ∨ (¬ p3954) ∨ (¬ p4041) ∨ (¬ p4348) ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h11082 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step42065 (p2027 p2295 p2954 p3097 p3646 p4336 : Prop)
    (h40810 : (¬ p2027))
    (h11083 : p2027 ∨ (¬ p2295) ∨ (¬ p2954) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4336))
    : (¬ p2295) ∨ (¬ p2954) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4336) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11083 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42066 (p2027 p2104 p2696 p3537 p3585 p4749 : Prop)
    (h40810 : (¬ p2027))
    (h11084 : p2027 ∨ (¬ p2104) ∨ (¬ p2696) ∨ (¬ p3537) ∨ (¬ p3585) ∨ (¬ p4749))
    : (¬ p2104) ∨ (¬ p2696) ∨ (¬ p3537) ∨ (¬ p3585) ∨ (¬ p4749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11084 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42067 (p2027 p2427 p3516 p3543 p4382 p4914 p4948 : Prop)
    (h40810 : (¬ p2027))
    (h11085 : p2027 ∨ (¬ p2427) ∨ (¬ p3516) ∨ (¬ p3543) ∨ (¬ p4382) ∨ (¬ p4914) ∨ (¬ p4948))
    : (¬ p2427) ∨ (¬ p3516) ∨ (¬ p3543) ∨ (¬ p4382) ∨ (¬ p4914) ∨ (¬ p4948) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3543 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4382 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4914 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h11085 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step42070 (p2027 p2156 p2982 p3954 p4110 p4242 p4340 p4450 p4521 : Prop)
    (h40810 : (¬ p2027))
    (h11088 : p2027 ∨ (¬ p2156) ∨ (¬ p2982) ∨ (¬ p3954) ∨ (¬ p4110) ∨ (¬ p4242) ∨ (¬ p4340) ∨ (¬ p4450) ∨ (¬ p4521))
    : (¬ p2156) ∨ (¬ p2982) ∨ (¬ p3954) ∨ (¬ p4110) ∨ (¬ p4242) ∨ (¬ p4340) ∨ (¬ p4450) ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h11088 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step42071 (p2027 p2749 p3027 p3361 p3414 p3585 p4749 : Prop)
    (h40810 : (¬ p2027))
    (h11089 : p2027 ∨ (¬ p2749) ∨ (¬ p3027) ∨ (¬ p3361) ∨ (¬ p3414) ∨ (¬ p3585) ∨ (¬ p4749))
    : (¬ p2749) ∨ (¬ p3027) ∨ (¬ p3361) ∨ (¬ p3414) ∨ (¬ p3585) ∨ (¬ p4749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2749 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h11089 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step42072 (p2027 p2230 p2264 p2274 p2563 p3548 p4361 p4366 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h11090 : p2027 ∨ (¬ p2230) ∨ (¬ p2264) ∨ (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3548) ∨ (¬ p4361) ∨ (¬ p4366) ∨ (¬ p5190))
    : (¬ p2230) ∨ (¬ p2264) ∨ (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3548) ∨ (¬ p4361) ∨ (¬ p4366) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h11090 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step42073 (p2027 p2156 p2264 p2427 p3548 p4110 p4362 p4366 p4521 : Prop)
    (h40810 : (¬ p2027))
    (h11091 : p2027 ∨ (¬ p2156) ∨ (¬ p2264) ∨ (¬ p2427) ∨ (¬ p3548) ∨ (¬ p4110) ∨ (¬ p4362) ∨ (¬ p4366) ∨ (¬ p4521))
    : (¬ p2156) ∨ (¬ p2264) ∨ (¬ p2427) ∨ (¬ p3548) ∨ (¬ p4110) ∨ (¬ p4362) ∨ (¬ p4366) ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h11091 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step42074 (p2027 p2449 p2761 p4025 p4191 p4361 : Prop)
    (h40810 : (¬ p2027))
    (h11092 : p2027 ∨ (¬ p2449) ∨ (¬ p2761) ∨ (¬ p4025) ∨ (¬ p4191) ∨ (¬ p4361))
    : (¬ p2449) ∨ (¬ p2761) ∨ (¬ p4025) ∨ (¬ p4191) ∨ (¬ p4361) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4025 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11092 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42075 (p2027 p2192 p2590 p3125 p4137 p4632 : Prop)
    (h40810 : (¬ p2027))
    (h11093 : p2027 ∨ (¬ p2192) ∨ (¬ p2590) ∨ (¬ p3125) ∨ (¬ p4137) ∨ (¬ p4632))
    : (¬ p2192) ∨ (¬ p2590) ∨ (¬ p3125) ∨ (¬ p4137) ∨ (¬ p4632) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11093 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42076 (p2027 p2264 p3955 p4019 p4361 p4441 p4800 p5568 : Prop)
    (h40810 : (¬ p2027))
    (h11094 : p2027 ∨ (¬ p2264) ∨ (¬ p3955) ∨ (¬ p4019) ∨ (¬ p4361) ∨ (¬ p4441) ∨ (¬ p4800) ∨ (¬ p5568))
    : (¬ p2264) ∨ (¬ p3955) ∨ (¬ p4019) ∨ (¬ p4361) ∨ (¬ p4441) ∨ (¬ p4800) ∨ (¬ p5568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4800 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h11094 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step42077 (p2027 p2299 p2737 p2911 p3365 p3389 p3588 p3873 p4477 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h11095 : p2027 ∨ (¬ p2299) ∨ (¬ p2737) ∨ (¬ p2911) ∨ (¬ p3365) ∨ (¬ p3389) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p4477) ∨ (¬ p5190))
    : (¬ p2299) ∨ (¬ p2737) ∨ (¬ p2911) ∨ (¬ p3365) ∨ (¬ p3389) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p4477) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h11095 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step42080 (p2027 p2406 p2589 p2608 p4108 p4376 : Prop)
    (h40810 : (¬ p2027))
    (h11098 : p2027 ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p4108) ∨ (¬ p4376))
    : (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p4108) ∨ (¬ p4376) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11098 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42081 (p2027 p2156 p2247 p2427 p2608 p2996 p3519 p4110 p4362 p4376 p4399 : Prop)
    (h40810 : (¬ p2027))
    (h11099 : p2027 ∨ (¬ p2156) ∨ (¬ p2247) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p2996) ∨ (¬ p3519) ∨ (¬ p4110) ∨ (¬ p4362) ∨ (¬ p4376) ∨ (¬ p4399))
    : (¬ p2156) ∨ (¬ p2247) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p2996) ∨ (¬ p3519) ∨ (¬ p4110) ∨ (¬ p4362) ∨ (¬ p4376) ∨ (¬ p4399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h11099 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step42083 (p2027 p2396 p2553 p2573 p2608 p3519 p3860 p3950 p4261 p4376 : Prop)
    (h40810 : (¬ p2027))
    (h11101 : p2027 ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4261) ∨ (¬ p4376))
    : (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4261) ∨ (¬ p4376) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h11101 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step42084 (p2027 p2166 p2608 p3369 p4120 p4377 : Prop)
    (h40810 : (¬ p2027))
    (h11102 : p2027 ∨ (¬ p2166) ∨ (¬ p2608) ∨ (¬ p3369) ∨ (¬ p4120) ∨ (¬ p4377))
    : (¬ p2166) ∨ (¬ p2608) ∨ (¬ p3369) ∨ (¬ p4120) ∨ (¬ p4377) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3369 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11102 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42085 (p2027 p2954 p3256 p3692 p4120 p4237 : Prop)
    (h40810 : (¬ p2027))
    (h11103 : p2027 ∨ (¬ p2954) ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4237))
    : (¬ p2954) ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4237) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2954 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4237 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11103 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42086 (p2027 p2589 p2839 p3585 p3695 p4727 : Prop)
    (h40810 : (¬ p2027))
    (h11104 : p2027 ∨ (¬ p2589) ∨ (¬ p2839) ∨ (¬ p3585) ∨ (¬ p3695) ∨ (¬ p4727))
    : (¬ p2589) ∨ (¬ p2839) ∨ (¬ p3585) ∨ (¬ p3695) ∨ (¬ p4727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11104 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42087 (p2027 p2247 p2470 p2528 p3497 p3662 p4348 p4905 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h11105 : p2027 ∨ (¬ p2247) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p4348) ∨ (¬ p4905) ∨ (¬ p5190))
    : (¬ p2247) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p4348) ∨ (¬ p4905) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h11105 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step42088 (p2027 p2122 p2579 p2588 p4375 p4727 : Prop)
    (h40810 : (¬ p2027))
    (h11106 : p2027 ∨ (¬ p2122) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p4375) ∨ (¬ p4727))
    : (¬ p2122) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p4375) ∨ (¬ p4727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11106 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42089 (p2027 p2177 p2553 p2573 p2743 p3877 p3954 p4041 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h11107 : p2027 ∨ (¬ p2177) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2743) ∨ (¬ p3877) ∨ (¬ p3954) ∨ (¬ p4041) ∨ (¬ p5190))
    : (¬ p2177) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2743) ∨ (¬ p3877) ∨ (¬ p3954) ∨ (¬ p4041) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h11107 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step42090 (p2027 p2177 p2553 p2573 p2737 p3365 p3873 p4041 p4242 p4963 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h11108 : p2027 ∨ (¬ p2177) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3873) ∨ (¬ p4041) ∨ (¬ p4242) ∨ (¬ p4963) ∨ (¬ p5190))
    : (¬ p2177) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3873) ∨ (¬ p4041) ∨ (¬ p4242) ∨ (¬ p4963) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h11108 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step42091 (p2027 p2177 p2553 p2573 p3256 p3365 p3873 p4041 p4340 p4364 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h11109 : p2027 ∨ (¬ p2177) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3256) ∨ (¬ p3365) ∨ (¬ p3873) ∨ (¬ p4041) ∨ (¬ p4340) ∨ (¬ p4364) ∨ (¬ p5190))
    : (¬ p2177) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3256) ∨ (¬ p3365) ∨ (¬ p3873) ∨ (¬ p4041) ∨ (¬ p4340) ∨ (¬ p4364) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h11109 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step42093 (p2027 p2470 p2528 p3583 p3694 p3954 p4348 p4905 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h11111 : p2027 ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3583) ∨ (¬ p3694) ∨ (¬ p3954) ∨ (¬ p4348) ∨ (¬ p4905) ∨ (¬ p5190))
    : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3583) ∨ (¬ p3694) ∨ (¬ p3954) ∨ (¬ p4348) ∨ (¬ p4905) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h11111 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step42094 (p2027 p2396 p2553 p2573 p3950 p3954 p4242 p4340 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h11112 : p2027 ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3950) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4340) ∨ (¬ p5190))
    : (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3950) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4340) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h11112 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step42095 (p2027 p2318 p2588 p2717 p3426 p3543 p3548 p5225 : Prop)
    (h40810 : (¬ p2027))
    (h11113 : p2027 ∨ (¬ p2318) ∨ (¬ p2588) ∨ (¬ p2717) ∨ (¬ p3426) ∨ (¬ p3543) ∨ (¬ p3548) ∨ (¬ p5225))
    : (¬ p2318) ∨ (¬ p2588) ∨ (¬ p2717) ∨ (¬ p3426) ∨ (¬ p3543) ∨ (¬ p3548) ∨ (¬ p5225) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2318 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3543 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5225 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h11113 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step42096 (p2027 p2911 p2922 p3551 p5191 p5197 : Prop)
    (h40810 : (¬ p2027))
    (h11114 : p2027 ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3551) ∨ (¬ p5191) ∨ (¬ p5197))
    : (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3551) ∨ (¬ p5191) ∨ (¬ p5197) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h11114 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step42098 (p2027 p2230 p2427 p2608 p3246 p3519 p3860 p3950 p4261 p4376 : Prop)
    (h40810 : (¬ p2027))
    (h11116 : p2027 ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p3246) ∨ (¬ p3519) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4261) ∨ (¬ p4376))
    : (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p3246) ∨ (¬ p3519) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4261) ∨ (¬ p4376) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h11116 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step42099 (p2027 p2230 p2247 p2427 p2608 p2881 p3519 p4041 p4360 p4376 : Prop)
    (h40810 : (¬ p2027))
    (h11117 : p2027 ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p2881) ∨ (¬ p3519) ∨ (¬ p4041) ∨ (¬ p4360) ∨ (¬ p4376))
    : (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p2881) ∨ (¬ p3519) ∨ (¬ p4041) ∨ (¬ p4360) ∨ (¬ p4376) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h11117 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step42100 (p2027 p2373 p2608 p3051 p3370 p3591 p3923 p4235 p4377 p4433 : Prop)
    (h40810 : (¬ p2027))
    (h11118 : p2027 ∨ (¬ p2373) ∨ (¬ p2608) ∨ (¬ p3051) ∨ (¬ p3370) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4235) ∨ (¬ p4377) ∨ (¬ p4433))
    : (¬ p2373) ∨ (¬ p2608) ∨ (¬ p3051) ∨ (¬ p3370) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4235) ∨ (¬ p4377) ∨ (¬ p4433) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h11118 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step42101 (p2027 p2245 p2470 p2528 p2641 p2963 p4041 p4348 p4360 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h11119 : p2027 ∨ (¬ p2245) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2641) ∨ (¬ p2963) ∨ (¬ p4041) ∨ (¬ p4348) ∨ (¬ p4360) ∨ (¬ p5190))
    : (¬ p2245) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2641) ∨ (¬ p2963) ∨ (¬ p4041) ∨ (¬ p4348) ∨ (¬ p4360) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h11119 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step42102 (p2027 p2230 p2427 p2748 p3246 p3365 p3873 p3950 p4118 p4360 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h11120 : p2027 ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2748) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p3873) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p5190))
    : (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2748) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p3873) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h11120 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step42103 (p2027 p2104 p2187 p2230 p2563 p3256 p3873 p4340 p4774 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h11121 : p2027 ∨ (¬ p2104) ∨ (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3256) ∨ (¬ p3873) ∨ (¬ p4340) ∨ (¬ p4774) ∨ (¬ p5190))
    : (¬ p2104) ∨ (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3256) ∨ (¬ p3873) ∨ (¬ p4340) ∨ (¬ p4774) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h11121 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step42104 (p2027 p2553 p2573 p2737 p3097 p3365 p3688 p3873 p4401 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h11122 : p2027 ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2737) ∨ (¬ p3097) ∨ (¬ p3365) ∨ (¬ p3688) ∨ (¬ p3873) ∨ (¬ p4401) ∨ (¬ p5190))
    : (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2737) ∨ (¬ p3097) ∨ (¬ p3365) ∨ (¬ p3688) ∨ (¬ p3873) ∨ (¬ p4401) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4401 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h11122 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

end ElevenRUP
