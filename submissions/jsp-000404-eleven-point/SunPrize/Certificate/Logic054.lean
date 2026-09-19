import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step102110 (p2470 p2528 p2577 p2797 p3286 p3292 p3567 p3680 p5059 p5284 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h72305 : (¬ p3680) ∨ (¬ p2470) ∨ (¬ p2797) ∨ (¬ p5059) ∨ (¬ p5284) ∨ (¬ p3567) ∨ (¬ p3292) ∨ (¬ p2577) ∨ (¬ p2528))
    : (¬ p5284) ∨ (¬ p3567) ∨ (¬ p2528) ∨ (¬ p5059) ∨ (¬ p2797) ∨ (¬ p2577) ∨ p3286 ∨ (¬ p2470) ∨ (¬ p3680) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h72305 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step102114 (p2156 p2563 p2982 p3680 p4110 p4399 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h46721 : (¬ p2156) ∨ (¬ p2982) ∨ (¬ p3680) ∨ (¬ p4110) ∨ (¬ p4399))
    : (¬ p2982) ∨ (¬ p4399) ∨ p2563 ∨ (¬ p2156) ∨ (¬ p3680) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46721 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step102115 (p2470 p2475 p2479 : Prop)
    (h73251 : p2470 ∨ (¬ p2479))
    (h3085 : p2475 ∨ p2479)
    : p2475 ∨ p2470 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2475) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2470) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2479) := (Or.elim h73251 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h3085 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102120 (p2248 p2608 p2651 p3083 p3599 p3670 p3954 p4149 p4379 p5119 p5387 : Prop)
    (h73572 : p4379 ∨ p3599)
    (h73498 : p3954 ∨ p2608)
    (h74026 : p5387 ∨ p3670)
    (h61691 : (¬ p2248) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p3954) ∨ (¬ p4149) ∨ (¬ p4379) ∨ (¬ p5119) ∨ (¬ p5387))
    : p3599 ∨ (¬ p4149) ∨ p2608 ∨ p3670 ∨ (¬ p2651) ∨ (¬ p5119) ∨ (¬ p2248) ∨ (¬ p3083) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3599) := (fun h => hn (Or.inl h));
    let u1 : p4149 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3670) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4379 := (Or.elim h73572 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61691 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u10)))))))))))))))))

theorem step102122 (p2246 p2651 p2744 p2761 p3083 p3366 p3425 p3434 p4149 p4324 p4381 p5119 : Prop)
    (h73556 : p4324 ∨ p3434)
    (h73574 : p4381 ∨ p2761)
    (h59451 : (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p4149) ∨ (¬ p4324) ∨ (¬ p4381) ∨ (¬ p5119))
    : (¬ p4149) ∨ (¬ p5119) ∨ (¬ p3425) ∨ (¬ p2744) ∨ p3434 ∨ (¬ p3366) ∨ (¬ p2246) ∨ (¬ p2651) ∨ p2761 ∨ (¬ p3083) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4149 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h59451 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (False.elim (r8 u1)))))))))))))))))))))

theorem step102128 (p2252 p2459 p2470 p2717 p2745 p2807 p2951 p3136 p3414 p3659 p3904 p4149 p4325 p4348 p5122 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h73392 : p3414 ∨ p2807)
    (h73562 : p4348 ∨ p2459)
    (h64910 : (¬ p2252) ∨ (¬ p2470) ∨ (¬ p2745) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p3414) ∨ (¬ p3659) ∨ (¬ p3904) ∨ (¬ p4149) ∨ (¬ p4325) ∨ (¬ p4348) ∨ (¬ p5122))
    : (¬ p4149) ∨ (¬ p2951) ∨ p2717 ∨ (¬ p3136) ∨ (¬ p2252) ∨ (¬ p2745) ∨ p2807 ∨ p2459 ∨ (¬ p2470) ∨ (¬ p3904) ∨ (¬ p4325) ∨ (¬ p5122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4149 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u13 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u14 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64910 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u14))) (fun r10 => (False.elim (r10 u11)))))))))))))))))))))))))

theorem step102129 (p3631 p5357 p6094 : Prop)
    (h74437 : p3631 ∨ (¬ p6094))
    (h13669 : p5357 ∨ p6094)
    : p5357 ∨ p3631 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5357) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3631) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6094) := (Or.elim h74437 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13669 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102130 (p3266 p5123 p6017 : Prop)
    (h74355 : (¬ p3266) ∨ (¬ p6017))
    (h13101 : p5123 ∨ p6017)
    : p5123 ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5123) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6017) := (Or.elim h74355 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13101 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102134 (p3005 p3755 p4009 p4035 p5107 p5122 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h63519 : (¬ p3005) ∨ (¬ p4009) ∨ (¬ p4035) ∨ (¬ p5107) ∨ (¬ p5122))
    : p3755 ∨ (¬ p4009) ∨ (¬ p5122) ∨ (¬ p3005) ∨ (¬ p5107) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3755) := (fun h => hn (Or.inl h));
    let u1 : p4009 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h63519 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step102135 (p2373 p4610 p5840 : Prop)
    (h74131 : (¬ p2373) ∨ (¬ p5840))
    (h12038 : p4610 ∨ p5840)
    : p4610 ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4610) := (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5840) := (Or.elim h74131 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12038 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102136 (p3083 p4121 p5978 : Prop)
    (h74307 : (¬ p3083) ∨ (¬ p5978))
    (h12859 : p4121 ∨ p5978)
    : p4121 ∨ (¬ p3083) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4121) := (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5978) := (Or.elim h74307 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12859 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102143 (p2254 p2449 p2608 p2761 p2807 p2829 p3414 p3914 p3947 p4381 p5250 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73494 : p3947 ∨ p2449)
    (h73392 : p3414 ∨ p2807)
    (h49074 : (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2829) ∨ (¬ p3414) ∨ (¬ p3914) ∨ (¬ p3947) ∨ (¬ p4381) ∨ (¬ p5250))
    : (¬ p3914) ∨ p2761 ∨ (¬ p5250) ∨ p2449 ∨ p2807 ∨ (¬ p2608) ∨ (¬ p2254) ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3914 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49074 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step102146 (p2774 p2780 p2829 p3599 p3670 p4379 p5387 : Prop)
    (h73572 : p4379 ∨ p3599)
    (h74026 : p5387 ∨ p3670)
    (h73308 : p2780 ∨ p2774)
    (h47446 : (¬ p2780) ∨ (¬ p2829) ∨ (¬ p4379) ∨ (¬ p5387))
    : p3599 ∨ p3670 ∨ p2774 ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3599) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3670) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4379 := (Or.elim h73572 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47446 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step102151 (p3399 p3434 p3830 p4324 p4366 p4797 p5362 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73556 : p4324 ∨ p3434)
    (h64843 : (¬ p3830) ∨ (¬ p4324) ∨ (¬ p4366) ∨ (¬ p4797) ∨ (¬ p5362))
    : (¬ p3830) ∨ p3399 ∨ (¬ p5362) ∨ p3434 ∨ (¬ p4797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3830 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h64843 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step102152 (p2717 p3434 p3945 p4324 : Prop)
    (h73556 : p4324 ∨ p3434)
    (h21746 : (¬ p2717) ∨ (¬ p3945) ∨ (¬ p4324))
    : p3434 ∨ (¬ p2717) ∨ (¬ p3945) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3945 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h21746 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step102155 (p2246 p2341 p2651 p2717 p2744 p3016 p3366 p3434 p3551 p3564 p3820 p4324 p4621 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73556 : p4324 ∨ p3434)
    (h64381 : (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2717) ∨ (¬ p2744) ∨ (¬ p3016) ∨ (¬ p3366) ∨ (¬ p3551) ∨ (¬ p3564) ∨ (¬ p3820) ∨ (¬ p4324) ∨ (¬ p4621))
    : (¬ p2717) ∨ (¬ p2246) ∨ p2341 ∨ (¬ p2744) ∨ (¬ p4621) ∨ (¬ p3820) ∨ p3434 ∨ (¬ p3366) ∨ (¬ p2651) ∨ (¬ p3564) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3820 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h64381 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (False.elim (r9 u4)))))))))))))))))))))))

theorem step102157 (p2751 p2996 p3027 p3434 p3516 p4066 p4324 p4781 : Prop)
    (h73556 : p4324 ∨ p3434)
    (h73340 : p3027 ∨ p2996)
    (h41444 : (¬ p2751) ∨ (¬ p3027) ∨ (¬ p3516) ∨ (¬ p4066) ∨ (¬ p4324) ∨ p4781)
    : p4781 ∨ (¬ p3516) ∨ (¬ p2751) ∨ (¬ p4066) ∨ p3434 ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4781) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u7 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41444 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (u0 r4)))))))))))))

theorem step102159 (p2230 p2373 p2761 p3425 p3434 p3969 p4324 p4381 p4419 p5119 : Prop)
    (h73556 : p4324 ∨ p3434)
    (h73574 : p4381 ∨ p2761)
    (h42382 : (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3425) ∨ (¬ p3969) ∨ (¬ p4324) ∨ (¬ p4381) ∨ (¬ p4419) ∨ (¬ p5119))
    : (¬ p3969) ∨ (¬ p5119) ∨ (¬ p4419) ∨ p3434 ∨ (¬ p3425) ∨ p2761 ∨ (¬ p2230) ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h42382 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step102162 (p2761 p2946 p3156 p3425 p3434 p3969 p4324 p4381 p4786 p5119 : Prop)
    (h73556 : p4324 ∨ p3434)
    (h73574 : p4381 ∨ p2761)
    (h41202 : (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3425) ∨ (¬ p3969) ∨ (¬ p4324) ∨ (¬ p4381) ∨ (¬ p4786) ∨ (¬ p5119))
    : p3434 ∨ p2761 ∨ (¬ p5119) ∨ (¬ p3969) ∨ (¬ p3425) ∨ (¬ p3156) ∨ (¬ p2946) ∨ (¬ p4786) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41202 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step102166 (p2192 p2210 p2761 p3425 p3434 p3737 p4324 p4381 p4736 p5250 : Prop)
    (h73556 : p4324 ∨ p3434)
    (h73574 : p4381 ∨ p2761)
    (h57893 : (¬ p2192) ∨ (¬ p2210) ∨ (¬ p3425) ∨ (¬ p3737) ∨ (¬ p4324) ∨ (¬ p4381) ∨ (¬ p4736) ∨ (¬ p5250))
    : (¬ p3737) ∨ (¬ p5250) ∨ (¬ p2192) ∨ (¬ p4736) ∨ p3434 ∨ (¬ p3425) ∨ (¬ p2210) ∨ p2761 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h57893 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step102167 (p2192 p2253 p2761 p2946 p3412 p3425 p3434 p3737 p4324 p4381 p4736 p5250 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73556 : p4324 ∨ p3434)
    (h49660 : (¬ p2192) ∨ (¬ p2253) ∨ (¬ p2946) ∨ (¬ p3412) ∨ (¬ p3425) ∨ (¬ p3737) ∨ (¬ p4324) ∨ (¬ p4381) ∨ (¬ p4736) ∨ (¬ p5250))
    : p2761 ∨ (¬ p3412) ∨ (¬ p4736) ∨ (¬ p2946) ∨ (¬ p5250) ∨ p3434 ∨ (¬ p2253) ∨ (¬ p2192) ∨ (¬ p3425) ∨ (¬ p3737) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h49660 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step102175 (p3093 p3319 p3449 p3591 p3990 p4026 p4503 p5307 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73504 : p4026 ∨ p3319)
    (h57197 : (¬ p3449) ∨ (¬ p3591) ∨ (¬ p3990) ∨ (¬ p4026) ∨ (¬ p4503) ∨ (¬ p5307))
    : p3093 ∨ (¬ p3449) ∨ p3319 ∨ (¬ p5307) ∨ (¬ p3990) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h57197 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step102176 (p3319 p3923 p3990 p4026 : Prop)
    (h73504 : p4026 ∨ p3319)
    (h33830 : p3923 ∨ (¬ p3990) ∨ (¬ p4026))
    : p3319 ∨ p3923 ∨ (¬ p3990) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3319) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3923) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h33830 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step102183 (p2156 p4356 p5792 : Prop)
    (h74067 : (¬ p2156) ∨ (¬ p5792))
    (h11759 : p4356 ∨ p5792)
    : p4356 ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4356) := (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5792) := (Or.elim h74067 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11759 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102189 (p2122 p4471 p5788 : Prop)
    (h74061 : p2122 ∨ (¬ p5788))
    (h11731 : p4471 ∨ p5788)
    : p4471 ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4471) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5788) := (Or.elim h74061 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11731 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102190 (p2850 p3698 p5932 : Prop)
    (h74249 : p2850 ∨ (¬ p5932))
    (h12576 : p3698 ∨ p5932)
    : p3698 ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3698) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5932) := (Or.elim h74249 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12576 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102194 (p2797 p4841 p5917 : Prop)
    (h74229 : p2797 ∨ (¬ p5917))
    (h12487 : p4841 ∨ p5917)
    : p4841 ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4841) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5917) := (Or.elim h74229 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12487 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102203 (p2860 p3985 p5936 : Prop)
    (h74255 : (¬ p2860) ∨ (¬ p5936))
    (h12600 : p3985 ∨ p5936)
    : p3985 ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3985) := (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5936) := (Or.elim h74255 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12600 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102207 (p4337 p4401 p4560 : Prop)
    (h72955 : p4560)
    (h26956 : (¬ p4337) ∨ p4401 ∨ (¬ p4560))
    : p4401 ∨ (¬ p4337) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4401) := (fun h => hn (Or.inl h));
    let u1 : p4337 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4560 := h72955;
    (Or.elim h26956 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step102210 (p2860 p4401 p5936 : Prop)
    (h74255 : (¬ p2860) ∨ (¬ p5936))
    (h12603 : p4401 ∨ p5936)
    : p4401 ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4401) := (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5936) := (Or.elim h74255 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12603 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102220 (p2774 p2786 p2789 : Prop)
    (h73313 : (¬ p2774) ∨ (¬ p2789))
    (h3701 : p2786 ∨ p2789)
    : p2786 ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2786) := (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2789) := (Or.elim h73313 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h3701 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102221 (p2396 p4396 p5845 : Prop)
    (h74137 : p2396 ∨ (¬ p5845))
    (h12064 : p4396 ∨ p5845)
    : p4396 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4396) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5845) := (Or.elim h74137 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12064 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102222 (p2396 p4620 p5845 : Prop)
    (h74137 : p2396 ∨ (¬ p5845))
    (h12067 : p4620 ∨ p5845)
    : p4620 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4620) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5845) := (Or.elim h74137 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12067 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102227 (p2774 p2785 p2789 : Prop)
    (h73313 : (¬ p2774) ∨ (¬ p2789))
    (h3703 : p2785 ∨ p2789)
    : p2785 ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2785) := (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2789) := (Or.elim h73313 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h3703 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102241 (p2341 p3551 p4905 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h54672 : (¬ p3551) ∨ p4905)
    : p2341 ∨ p4905 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4905) := (fun h => hn (Or.inr h));
    let u2 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h54672 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step102242 (p2341 p2881 p3212 p3551 p3872 p4984 p5046 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h52382 : (¬ p2881) ∨ (¬ p3212) ∨ (¬ p3551) ∨ (¬ p3872) ∨ (¬ p4984) ∨ (¬ p5046))
    : p2341 ∨ (¬ p3212) ∨ (¬ p3872) ∨ (¬ p5046) ∨ (¬ p2881) ∨ (¬ p4984) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5046 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h52382 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step102247 (p2246 p2341 p2651 p2749 p2881 p3016 p3246 p3546 p3551 p3564 p3690 p4330 p4445 p4796 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73446 : p3690 ∨ p3246)
    (h53278 : (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2749) ∨ (¬ p2881) ∨ (¬ p3016) ∨ (¬ p3546) ∨ (¬ p3551) ∨ (¬ p3564) ∨ (¬ p3690) ∨ (¬ p4330) ∨ (¬ p4445) ∨ (¬ p4796))
    : (¬ p3546) ∨ (¬ p3564) ∨ (¬ p2749) ∨ (¬ p2246) ∨ (¬ p4796) ∨ p2341 ∨ p3246 ∨ (¬ p2651) ∨ (¬ p2881) ∨ (¬ p4445) ∨ (¬ p3016) ∨ (¬ p4330) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3546 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4796 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h53278 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u13))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u11))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u4)))))))))))))))))))))))))

theorem step102248 (p2132 p2341 p2459 p2860 p3266 p3551 p3737 p4348 p4444 p4729 p5197 p5250 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73580 : p4444 ∨ p3266)
    (h73562 : p4348 ∨ p2459)
    (h50771 : (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3551) ∨ (¬ p3737) ∨ (¬ p4348) ∨ (¬ p4444) ∨ (¬ p4729) ∨ (¬ p5197) ∨ (¬ p5250))
    : (¬ p3737) ∨ (¬ p2860) ∨ p2341 ∨ p3266 ∨ (¬ p2132) ∨ (¬ p5250) ∨ (¬ p5197) ∨ p2459 ∨ (¬ p4729) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h50771 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step102249 (p2553 p3581 p5875 : Prop)
    (h74173 : p2553 ∨ (¬ p5875))
    (h12242 : p3581 ∨ p5875)
    : p3581 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3581) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5875) := (Or.elim h74173 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12242 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102250 (p2352 p4596 p5833 : Prop)
    (h74121 : p2352 ∨ (¬ p5833))
    (h11995 : p4596 ∨ p5833)
    : p4596 ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4596) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2352) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5833) := (Or.elim h74121 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11995 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102251 (p2363 p4603 p5837 : Prop)
    (h74127 : (¬ p2363) ∨ (¬ p5837))
    (h12019 : p4603 ∨ p5837)
    : p4603 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4603) := (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5837) := (Or.elim h74127 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12019 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102252 (p3193 p3227 p3230 : Prop)
    (h73367 : (¬ p3193) ∨ (¬ p3230))
    (h4578 : p3227 ∨ p3230)
    : p3227 ∨ (¬ p3193) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3227) := (fun h => hn (Or.inl h));
    let u1 : p3193 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3230) := (Or.elim h73367 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h4578 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102253 (p2241 p2247 p3266 p3506 p3830 p3853 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73226 : p2247 ∨ p2241)
    (h45070 : (¬ p2247) ∨ (¬ p3506) ∨ (¬ p3830) ∨ (¬ p3853) ∨ (¬ p4444))
    : p3266 ∨ (¬ p3853) ∨ p2241 ∨ (¬ p3506) ∨ (¬ p3830) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3853 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45070 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step102254 (p2241 p2247 p2751 p3755 p3830 p3853 p4035 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73506 : p4035 ∨ p3755)
    (h61237 : (¬ p2247) ∨ (¬ p2751) ∨ (¬ p3830) ∨ (¬ p3853) ∨ (¬ p4035))
    : p2241 ∨ (¬ p3853) ∨ (¬ p2751) ∨ (¬ p3830) ∨ p3755 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p3853 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h61237 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step102256 (p2406 p4202 p5848 : Prop)
    (h74141 : p2406 ∨ (¬ p5848))
    (h12082 : p4202 ∨ p5848)
    : p4202 ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4202) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2406) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5848) := (Or.elim h74141 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12082 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102259 (p2641 p4756 p5893 : Prop)
    (h74197 : p2641 ∨ (¬ p5893))
    (h12345 : p4756 ∨ p5893)
    : p4756 ∨ p2641 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4756) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5893) := (Or.elim h74197 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12345 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102260 (p2192 p4338 p5804 : Prop)
    (h74083 : (¬ p2192) ∨ (¬ p5804))
    (h11824 : p4338 ∨ p5804)
    : p4338 ∨ (¬ p2192) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4338) := (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5804) := (Or.elim h74083 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11824 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102268 (p2166 p4496 p5795 : Prop)
    (h74071 : (¬ p2166) ∨ (¬ p5795))
    (h11773 : p4496 ∨ p5795)
    : p4496 ∨ (¬ p2166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4496) := (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5795) := (Or.elim h74071 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11773 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102269 (p3527 p3544 p6076 : Prop)
    (h74417 : p3527 ∨ (¬ p6076))
    (h13486 : p3544 ∨ p6076)
    : p3544 ∨ p3527 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3544) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3527) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6076) := (Or.elim h74417 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13486 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102271 (p2982 p4951 p4953 : Prop)
    (h73848 : p4951 ∨ (¬ p2982))
    (h8230 : (¬ p4951) ∨ p4953)
    : (¬ p2982) ∨ p4953 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4953) := (fun h => hn (Or.inr h));
    let u2 : p4951 := (Or.elim h73848 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h8230 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step102279 (p2220 p2440 p2542 p3016 p3096 p3574 p4109 p4509 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73422 : p3574 ∨ p3016)
    (h61866 : (¬ p2220) ∨ (¬ p2542) ∨ (¬ p3096) ∨ (¬ p3574) ∨ (¬ p4109) ∨ (¬ p4509))
    : p2440 ∨ p3016 ∨ (¬ p4109) ∨ (¬ p4509) ∨ (¬ p3096) ∨ (¬ p2220) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h61866 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step102285 (p2829 p4024 p5927 : Prop)
    (h74243 : (¬ p2829) ∨ (¬ p5927))
    (h12550 : p4024 ∨ p5927)
    : p4024 ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4024) := (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5927) := (Or.elim h74243 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12550 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102286 (p2641 p4757 p5893 : Prop)
    (h74197 : p2641 ∨ (¬ p5893))
    (h12344 : p4757 ∨ p5893)
    : p4757 ∨ p2641 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4757) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5893) := (Or.elim h74197 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12344 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102287 (p2241 p2252 p2256 : Prop)
    (h73231 : (¬ p2241) ∨ (¬ p2256))
    (h2647 : p2252 ∨ p2256)
    : p2252 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2252) := (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2256) := (Or.elim h73231 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h2647 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102297 (p2829 p4869 p5927 : Prop)
    (h74243 : (¬ p2829) ∨ (¬ p5927))
    (h12551 : p4869 ∨ p5927)
    : p4869 ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4869) := (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5927) := (Or.elim h74243 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12551 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102298 (p2797 p4842 p5917 : Prop)
    (h74229 : p2797 ∨ (¬ p5917))
    (h12488 : p4842 ∨ p5917)
    : p4842 ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4842) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5917) := (Or.elim h74229 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12488 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102299 (p2187 p3988 p5800 : Prop)
    (h74077 : p2187 ∨ (¬ p5800))
    (h11802 : p3988 ∨ p5800)
    : p3988 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3988) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2187) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5800) := (Or.elim h74077 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11802 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102304 (p2241 p2247 p2751 p3005 p3449 p3877 p4288 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73488 : p3877 ∨ p3005)
    (h41582 : (¬ p2247) ∨ (¬ p2751) ∨ (¬ p3449) ∨ (¬ p3877) ∨ (¬ p4288))
    : (¬ p3449) ∨ p2241 ∨ (¬ p4288) ∨ (¬ p2751) ∨ p3005 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4288 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41582 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step102305 (p2156 p2187 p2241 p2247 p2363 p3449 p3645 p3646 p3989 p4181 p4347 p4959 p5122 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73436 : p3646 ∨ p2156)
    (h73226 : p2247 ∨ p2241)
    (h73502 : p3989 ∨ p2187)
    (h52547 : (¬ p2247) ∨ (¬ p3449) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4181) ∨ (¬ p4347) ∨ (¬ p4959) ∨ (¬ p5122))
    : (¬ p4181) ∨ p2363 ∨ p2156 ∨ (¬ p3645) ∨ (¬ p3449) ∨ (¬ p5122) ∨ (¬ p4959) ∨ p2241 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4181 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h52547 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step102307 (p2210 p2696 p2797 p3073 p3323 p3365 p3366 p3449 p3555 p4037 p4195 p4377 p4604 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73532 : p4195 ∨ p2797)
    (h73412 : p3555 ∨ p2210)
    (h73390 : p3365 ∨ p2696)
    (h42385 : (¬ p3073) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3555) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p4377) ∨ (¬ p4604))
    : (¬ p3073) ∨ (¬ p3449) ∨ p3323 ∨ (¬ p4377) ∨ p2797 ∨ (¬ p4604) ∨ (¬ p3366) ∨ p2210 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h42385 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step102311 (p2717 p3146 p3366 p3379 p3425 p3449 p3452 p3659 p3692 p4042 p4181 p4376 p5122 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73448 : p3692 ∨ p3146)
    (h73438 : p3659 ∨ p2717)
    (h64899 : (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p3659) ∨ (¬ p3692) ∨ (¬ p4042) ∨ (¬ p4181) ∨ (¬ p4376) ∨ (¬ p5122))
    : (¬ p4181) ∨ p3379 ∨ (¬ p5122) ∨ (¬ p3425) ∨ (¬ p3449) ∨ p3146 ∨ (¬ p4042) ∨ (¬ p3366) ∨ (¬ p4376) ∨ p2717 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4181 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h64899 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step102312 (p2608 p3449 p3954 p4181 p5558 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h45163 : (¬ p3449) ∨ (¬ p3954) ∨ (¬ p4181) ∨ (¬ p5558))
    : (¬ p4181) ∨ p2608 ∨ (¬ p3449) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4181 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45163 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step102320 (p2850 p3054 p5932 : Prop)
    (h74249 : p2850 ∨ (¬ p5932))
    (h12578 : p3054 ∨ p5932)
    : p3054 ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3054) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5932) := (Or.elim h74249 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12578 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102325 (p2156 p2220 p2563 p3646 p3969 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h45725 : (¬ p2220) ∨ (¬ p2563) ∨ (¬ p3646) ∨ (¬ p3969))
    : (¬ p3969) ∨ (¬ p2220) ∨ (¬ p2563) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45725 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step102327 (p2220 p4115 p4530 : Prop)
    (h73620 : p4530 ∨ (¬ p2220))
    (h7128 : p4115 ∨ (¬ p4530))
    : p4115 ∨ (¬ p2220) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4115) := (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4530 := (Or.elim h73620 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h7128 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step102333 (p2891 p3571 p5945 : Prop)
    (h74267 : (¬ p2891) ∨ (¬ p5945))
    (h12653 : p3571 ∨ p5945)
    : p3571 ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3571) := (fun h => hn (Or.inl h));
    let u1 : p2891 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5945) := (Or.elim h74267 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12653 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102334 (p2870 p3587 p5939 : Prop)
    (h74259 : (¬ p2870) ∨ (¬ p5939))
    (h12618 : p3587 ∨ p5939)
    : p3587 ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3587) := (fun h => hn (Or.inl h));
    let u1 : p2870 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5939) := (Or.elim h74259 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12618 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102335 (p2437 p3580 p5858 : Prop)
    (h74155 : (¬ p2437) ∨ (¬ p5858))
    (h12141 : p3580 ∨ p5858)
    : p3580 ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3580) := (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5858) := (Or.elim h74155 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12141 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102345 (p2651 p2659 p2660 : Prop)
    (h73289 : p2651 ∨ (¬ p2660))
    (h3439 : p2659 ∨ p2660)
    : p2659 ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2659) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2660) := (Or.elim h73289 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h3439 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102346 (p2911 p4922 p5950 : Prop)
    (h74273 : p2911 ∨ (¬ p5950))
    (h12684 : p4922 ∨ p5950)
    : p4922 ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4922) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2911) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5950) := (Or.elim h74273 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12684 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102352 (p3422 p4342 p6049 : Prop)
    (h74389 : p3422 ∨ (¬ p6049))
    (h13290 : p4342 ∨ p6049)
    : p4342 ∨ p3422 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4342) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6049) := (Or.elim h74389 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13290 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102353 (p2829 p4871 p5927 : Prop)
    (h74243 : (¬ p2829) ∨ (¬ p5927))
    (h12548 : p4871 ∨ p5927)
    : p4871 ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4871) := (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5927) := (Or.elim h74243 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12548 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102356 (p3246 p4395 p6010 : Prop)
    (h74345 : p3246 ∨ (¬ p6010))
    (h13057 : p4395 ∨ p6010)
    : p4395 ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4395) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6010) := (Or.elim h74345 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13057 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102357 (p2166 p2210 p2774 p2780 p3461 p3917 p3969 p4191 p4736 p5119 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73308 : p2780 ∨ p2774)
    (h60366 : (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2780) ∨ (¬ p3917) ∨ (¬ p3969) ∨ (¬ p4191) ∨ (¬ p4736) ∨ (¬ p5119))
    : (¬ p3969) ∨ p3461 ∨ p2774 ∨ (¬ p2166) ∨ (¬ p5119) ∨ (¬ p3917) ∨ (¬ p4736) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h60366 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step102361 (p3461 p5252 p6059 : Prop)
    (h74403 : (¬ p3461) ∨ (¬ p6059))
    (h13359 : p5252 ∨ p6059)
    : p5252 ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5252) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6059) := (Or.elim h74403 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13359 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102362 (p3461 p4394 p6059 : Prop)
    (h74403 : (¬ p3461) ∨ (¬ p6059))
    (h13360 : p4394 ∨ p6059)
    : p4394 ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4394) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6059) := (Or.elim h74403 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13360 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102363 (p3461 p5253 p6059 : Prop)
    (h74403 : (¬ p3461) ∨ (¬ p6059))
    (h13362 : p5253 ∨ p6059)
    : p5253 ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5253) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6059) := (Or.elim h74403 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13362 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102364 (p3461 p5254 p6059 : Prop)
    (h74403 : (¬ p3461) ∨ (¬ p6059))
    (h13363 : p5254 ∨ p6059)
    : p5254 ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5254) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6059) := (Or.elim h74403 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13363 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102372 (p2230 p2427 p3246 p3286 p3292 p3670 p4236 p4419 p5236 p5284 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h42596 : (¬ p2230) ∨ (¬ p2427) ∨ (¬ p3246) ∨ (¬ p3292) ∨ (¬ p3670) ∨ (¬ p4236) ∨ (¬ p4419) ∨ (¬ p5236) ∨ (¬ p5284))
    : (¬ p3670) ∨ (¬ p5284) ∨ p3286 ∨ (¬ p4236) ∨ (¬ p2427) ∨ (¬ p2230) ∨ (¬ p3246) ∨ (¬ p5236) ∨ (¬ p4419) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3670 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42596 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step102373 (p2246 p2352 p2383 p2387 p2749 p2761 p2807 p3096 p3125 p3506 p3645 p3744 p4198 p4202 p4381 p4625 p4661 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h73574 : p4381 ∨ p2761)
    (h73454 : p3744 ∨ p3125)
    (h72310 : (¬ p3506) ∨ (¬ p3744) ∨ (¬ p4625) ∨ (¬ p2387) ∨ (¬ p2246) ∨ (¬ p2807) ∨ (¬ p4381) ∨ (¬ p3645) ∨ (¬ p4661) ∨ (¬ p3096) ∨ (¬ p4198) ∨ (¬ p2352) ∨ (¬ p2749) ∨ (¬ p4202))
    : (¬ p4661) ∨ (¬ p2352) ∨ (¬ p4625) ∨ (¬ p4198) ∨ p2383 ∨ p2761 ∨ (¬ p2246) ∨ p3125 ∨ (¬ p3506) ∨ (¬ p3096) ∨ (¬ p3645) ∨ (¬ p2807) ∨ (¬ p2749) ∨ (¬ p4202) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4661 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))));
    let u14 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u15 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u16 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h72310 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u16))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u14))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u15))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u3))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u1))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u12))) (fun r12 => (False.elim (r12 u13)))))))))))))))))))))))))))))

theorem step102376 (p3343 p5176 p6032 : Prop)
    (h74371 : (¬ p3343) ∨ (¬ p6032))
    (h13186 : p5176 ∨ p6032)
    : p5176 ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5176) := (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6032) := (Or.elim h74371 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13186 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102381 (p2230 p2252 p2331 p2373 p2741 p2963 p3323 p3461 p3519 p3969 p4037 p4191 p4376 p5119 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73338 : p2963 ∨ p2331)
    (h73508 : p4037 ∨ p3323)
    (h57493 : (¬ p2230) ∨ (¬ p2252) ∨ (¬ p2373) ∨ (¬ p2741) ∨ (¬ p2963) ∨ (¬ p3519) ∨ (¬ p3969) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4376) ∨ (¬ p5119))
    : (¬ p3969) ∨ p3461 ∨ p2331 ∨ (¬ p4376) ∨ (¬ p2373) ∨ (¬ p5119) ∨ (¬ p2741) ∨ p3323 ∨ (¬ p2230) ∨ (¬ p3519) ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u13 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h57493 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u13))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u3))) (fun r9 => (False.elim (r9 u5)))))))))))))))))))))))

theorem step102382 (p2717 p3434 p3969 p4132 p4324 p4445 p5122 : Prop)
    (h73556 : p4324 ∨ p3434)
    (h58310 : (¬ p2717) ∨ (¬ p3969) ∨ (¬ p4132) ∨ (¬ p4324) ∨ (¬ p4445) ∨ (¬ p5122))
    : p3434 ∨ (¬ p2717) ∨ (¬ p4445) ∨ (¬ p5122) ∨ (¬ p3969) ∨ (¬ p4132) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h58310 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step102383 (p2230 p2373 p2696 p3005 p3256 p3365 p3877 p3969 p4118 p4419 p5122 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73520 : p4118 ∨ p3256)
    (h73390 : p3365 ∨ p2696)
    (h48261 : (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p3969) ∨ (¬ p4118) ∨ (¬ p4419) ∨ (¬ p5122))
    : (¬ p3969) ∨ (¬ p5122) ∨ (¬ p4419) ∨ p3005 ∨ (¬ p2230) ∨ p3256 ∨ (¬ p2373) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h48261 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step102384 (p2230 p2246 p2331 p2373 p2741 p2963 p3323 p3461 p3519 p3969 p4037 p4191 p4376 p5119 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73338 : p2963 ∨ p2331)
    (h73530 : p4191 ∨ p3461)
    (h57346 : (¬ p2230) ∨ p2246 ∨ (¬ p2373) ∨ (¬ p2741) ∨ (¬ p2963) ∨ (¬ p3519) ∨ (¬ p3969) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4376) ∨ (¬ p5119))
    : (¬ p3969) ∨ p2246 ∨ (¬ p2741) ∨ p3323 ∨ (¬ p3519) ∨ (¬ p2230) ∨ p2331 ∨ (¬ p2373) ∨ p3461 ∨ (¬ p4376) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h57346 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u13))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (False.elim (r9 u10)))))))))))))))))))))))

theorem step102388 (p3399 p3546 p6044 : Prop)
    (h74383 : (¬ p3399) ∨ (¬ p6044))
    (h13262 : p3546 ∨ p6044)
    : p3546 ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3546) := (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6044) := (Or.elim h74383 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13262 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102391 (p2406 p4629 p5848 : Prop)
    (h74141 : p2406 ∨ (¬ p5848))
    (h12085 : p4629 ∨ p5848)
    : p4629 ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4629) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2406) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5848) := (Or.elim h74141 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12085 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102393 (p2493 p2500 p2502 : Prop)
    (h73261 : p2493 ∨ (¬ p2502))
    (h3132 : p2500 ∨ p2502)
    : p2500 ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2500) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2493) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2502) := (Or.elim h73261 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h3132 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102400 (p3083 p5011 p5978 : Prop)
    (h74307 : (¬ p3083) ∨ (¬ p5978))
    (h12861 : p5011 ∨ p5978)
    : p5011 ∨ (¬ p3083) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5011) := (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5978) := (Or.elim h74307 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12861 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102401 (p3083 p5012 p5978 : Prop)
    (h74307 : (¬ p3083) ∨ (¬ p5978))
    (h12862 : p5012 ∨ p5978)
    : p5012 ∨ (¬ p3083) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5012) := (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5978) := (Or.elim h74307 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12862 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102402 (p2992 p4957 p5959 : Prop)
    (h74285 : p2992 ∨ (¬ p5959))
    (h12741 : p4957 ∨ p5959)
    : p4957 ∨ p2992 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4957) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5959) := (Or.elim h74285 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12741 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102406 (p2749 p2839 p3005 p3189 p3583 p3877 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73424 : p3583 ∨ p2839)
    (h67277 : (¬ p2749) ∨ (¬ p3877) ∨ (¬ p3189) ∨ (¬ p3583))
    : p3005 ∨ (¬ p3189) ∨ (¬ p2749) ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h67277 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step102409 (p2246 p2749 p2807 p3599 p4379 p4777 p5234 : Prop)
    (h73572 : p4379 ∨ p3599)
    (h20675 : (¬ p2246) ∨ (¬ p2749) ∨ (¬ p2807) ∨ (¬ p4379) ∨ (¬ p4777) ∨ (¬ p5234))
    : p3599 ∨ (¬ p2246) ∨ (¬ p2749) ∨ (¬ p5234) ∨ (¬ p2807) ∨ (¬ p4777) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3599) := (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5234 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4777 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4379 := (Or.elim h73572 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h20675 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step102413 (p2210 p4525 p5807 : Prop)
    (h74087 : (¬ p2210) ∨ (¬ p5807))
    (h11845 : p4525 ∨ p5807)
    : p4525 ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4525) := (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5807) := (Or.elim h74087 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11845 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102415 (p3051 p4987 p4988 : Prop)
    (h73866 : p4987 ∨ (¬ p3051))
    (h8320 : (¬ p4987) ∨ p4988)
    : (¬ p3051) ∨ p4988 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4988) := (fun h => hn (Or.inr h));
    let u2 : p4987 := (Or.elim h73866 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h8320 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step102417 (p2210 p4172 p5807 : Prop)
    (h74087 : (¬ p2210) ∨ (¬ p5807))
    (h11844 : p4172 ∨ p5807)
    : p4172 ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4172) := (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5807) := (Or.elim h74087 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11844 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102418 (p2166 p4446 p5795 : Prop)
    (h74071 : (¬ p2166) ∨ (¬ p5795))
    (h11772 : p4446 ∨ p5795)
    : p4446 ∨ (¬ p2166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4446) := (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5795) := (Or.elim h74071 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11772 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102419 (p3051 p4283 p5969 : Prop)
    (h74299 : (¬ p3051) ∨ (¬ p5969))
    (h12810 : p4283 ∨ p5969)
    : p4283 ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4283) := (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5969) := (Or.elim h74299 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12810 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102421 (p2307 p2797 p3005 p3567 p3877 p4769 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h72312 : (¬ p3877) ∨ (¬ p4769) ∨ (¬ p3567) ∨ (¬ p2307) ∨ (¬ p2797))
    : (¬ p3567) ∨ p3005 ∨ (¬ p2307) ∨ (¬ p4769) ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3567 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4769 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h72312 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step102424 (p2177 p2299 p2319 p2341 p3323 p3567 p4037 p4620 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h73508 : p4037 ∨ p3323)
    (h48301 : (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p3567) ∨ (¬ p4037) ∨ (¬ p4620))
    : (¬ p2341) ∨ (¬ p2319) ∨ (¬ p4620) ∨ p2177 ∨ p3323 ∨ (¬ p3567) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48301 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step102427 (p2132 p2137 p2141 : Prop)
    (h73215 : p2132 ∨ (¬ p2141))
    (h2416 : p2137 ∨ p2141)
    : p2137 ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2137) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2141) := (Or.elim h73215 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h2416 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102428 (p3093 p5020 p5981 : Prop)
    (h74311 : (¬ p3093) ∨ (¬ p5981))
    (h12879 : p5020 ∨ p5981)
    : p5020 ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5020) := (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5981) := (Or.elim h74311 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12879 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102429 (p2264 p3919 p5815 : Prop)
    (h74097 : p2264 ∨ (¬ p5815))
    (h11890 : p3919 ∨ p5815)
    : p3919 ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3919) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2264) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5815) := (Or.elim h74097 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11890 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102431 (p2220 p4115 p5810 : Prop)
    (h74091 : (¬ p2220) ∨ (¬ p5810))
    (h11863 : p4115 ∨ p5810)
    : p4115 ∨ (¬ p2220) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4115) := (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5810) := (Or.elim h74091 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11863 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102432 (p2797 p2951 p3136 p3212 p3745 p4195 p5046 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h52760 : (¬ p2951) ∨ (¬ p3136) ∨ (¬ p3212) ∨ (¬ p3745) ∨ (¬ p4195) ∨ (¬ p5046))
    : p2797 ∨ (¬ p3136) ∨ (¬ p2951) ∨ (¬ p3212) ∨ (¬ p5046) ∨ (¬ p3745) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5046 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h52760 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step102434 (p2992 p4448 p5959 : Prop)
    (h74285 : p2992 ∨ (¬ p5959))
    (h12738 : p4448 ∨ p5959)
    : p4448 ∨ p2992 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4448) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5959) := (Or.elim h74285 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12738 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102435 (p3125 p4397 p5989 : Prop)
    (h74321 : p3125 ∨ (¬ p5989))
    (h12926 : p4397 ∨ p5989)
    : p4397 ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4397) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5989) := (Or.elim h74321 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12926 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102437 (p3166 p3171 p3175 : Prop)
    (h73357 : p3166 ∨ (¬ p3175))
    (h4466 : p3171 ∨ p3175)
    : p3171 ∨ p3166 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3171) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr h));
    let u2 : (¬ p3175) := (Or.elim h73357 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h4466 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102439 (p3005 p4364 p5962 : Prop)
    (h74289 : p3005 ∨ (¬ p5962))
    (h12761 : p4364 ∨ p5962)
    : p4364 ∨ p3005 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4364) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5962) := (Or.elim h74289 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12761 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102442 (p2807 p4849 p5920 : Prop)
    (h74233 : p2807 ∨ (¬ p5920))
    (h12504 : p4849 ∨ p5920)
    : p4849 ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4849) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2807) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5920) := (Or.elim h74233 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12504 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102443 (p2807 p4850 p5920 : Prop)
    (h74233 : p2807 ∨ (¬ p5920))
    (h12505 : p4850 ∨ p5920)
    : p4850 ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4850) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2807) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5920) := (Or.elim h74233 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12505 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102447 (p2819 p4078 p5923 : Prop)
    (h74237 : p2819 ∨ (¬ p5923))
    (h12526 : p4078 ∨ p5923)
    : p4078 ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4078) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5923) := (Or.elim h74237 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12526 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102450 (p2331 p2363 p2641 p2811 p3005 p3877 p4154 p4347 p4769 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73560 : p4347 ∨ p2363)
    (h73526 : p4154 ∨ p2641)
    (h57924 : (¬ p2331) ∨ (¬ p2811) ∨ (¬ p3877) ∨ (¬ p4154) ∨ (¬ p4347) ∨ (¬ p4769))
    : p3005 ∨ p2363 ∨ (¬ p2811) ∨ (¬ p4769) ∨ p2641 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4769 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h57924 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step102454 (p2797 p3005 p3877 p4228 p4769 p5586 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h42212 : (¬ p2797) ∨ (¬ p3877) ∨ (¬ p4228) ∨ (¬ p4769) ∨ (¬ p5586))
    : (¬ p4228) ∨ (¬ p5586) ∨ (¬ p2797) ∨ (¬ p4769) ∨ p3005 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4228 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5586 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4769 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42212 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step102461 (p3005 p4963 p5962 : Prop)
    (h74289 : p3005 ∨ (¬ p5962))
    (h12759 : p4963 ∨ p5962)
    : p4963 ∨ p3005 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4963) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5962) := (Or.elim h74289 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12759 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102464 (p3449 p5242 p6056 : Prop)
    (h74399 : (¬ p3449) ∨ (¬ p6056))
    (h13341 : p5242 ∨ p6056)
    : p5242 ∨ (¬ p3449) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5242) := (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6056) := (Or.elim h74399 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13341 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102465 (p2132 p2138 p4232 p5025 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h31905 : (¬ p2138) ∨ p4232 ∨ (¬ p5025))
    : p4232 ∨ p2132 ∨ (¬ p5025) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4232) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5025 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h31905 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step102471 (p3319 p5148 p6025 : Prop)
    (h74365 : p3319 ∨ (¬ p6025))
    (h13144 : p5148 ∨ p6025)
    : p5148 ∨ p3319 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5148) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3319) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6025) := (Or.elim h74365 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13144 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102478 (p3599 p5327 p5329 : Prop)
    (h74004 : p5327 ∨ p3599)
    (h9159 : (¬ p5327) ∨ p5329)
    : p3599 ∨ p5329 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3599) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5329) := (fun h => hn (Or.inr h));
    let u2 : p5327 := (Or.elim h74004 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h9159 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step102480 (p3599 p4029 p6085 : Prop)
    (h74429 : p3599 ∨ (¬ p6085))
    (h13618 : p4029 ∨ p6085)
    : p4029 ∨ p3599 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4029) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3599) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6085) := (Or.elim h74429 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13618 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102484 (p3156 p4311 p5999 : Prop)
    (h74335 : (¬ p3156) ∨ (¬ p5999))
    (h12980 : p4311 ∨ p5999)
    : p4311 ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4311) := (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5999) := (Or.elim h74335 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12980 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102487 (p2449 p4429 p5860 : Prop)
    (h74157 : p2449 ∨ (¬ p5860))
    (h12153 : p4429 ∨ p5860)
    : p4429 ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4429) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5860) := (Or.elim h74157 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12153 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102489 (p2449 p4656 p5860 : Prop)
    (h74157 : p2449 ∨ (¬ p5860))
    (h12151 : p4656 ∨ p5860)
    : p4656 ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4656) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5860) := (Or.elim h74157 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12151 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102490 (p3051 p4988 p5969 : Prop)
    (h74299 : (¬ p3051) ∨ (¬ p5969))
    (h12808 : p4988 ∨ p5969)
    : p4988 ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4988) := (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5969) := (Or.elim h74299 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12808 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102492 (p3146 p4450 p5995 : Prop)
    (h74329 : p3146 ∨ (¬ p5995))
    (h12961 : p4450 ∨ p5995)
    : p4450 ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4450) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5995) := (Or.elim h74329 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12961 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102493 (p2230 p3904 p5812 : Prop)
    (h74093 : p2230 ∨ (¬ p5812))
    (h11874 : p3904 ∨ p5812)
    : p3904 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3904) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2230) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5812) := (Or.elim h74093 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11874 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102494 (p3256 p4349 p6013 : Prop)
    (h74349 : p3256 ∨ (¬ p6013))
    (h13075 : p4349 ∨ p6013)
    : p4349 ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4349) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6013) := (Or.elim h74349 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13075 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102495 (p3256 p5107 p6013 : Prop)
    (h74349 : p3256 ∨ (¬ p6013))
    (h13073 : p5107 ∨ p6013)
    : p5107 ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5107) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6013) := (Or.elim h74349 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13073 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102496 (p2352 p3573 p5833 : Prop)
    (h74121 : p2352 ∨ (¬ p5833))
    (h11993 : p3573 ∨ p5833)
    : p3573 ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3573) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2352) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5833) := (Or.elim h74121 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11993 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102499 (p2187 p2573 p2579 p3737 p3989 p5514 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73502 : p3989 ∨ p2187)
    (h43053 : (¬ p2579) ∨ (¬ p3737) ∨ (¬ p3989) ∨ (¬ p5514))
    : (¬ p3737) ∨ (¬ p5514) ∨ p2573 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43053 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step102500 (p3146 p3256 p4118 p4196 p4228 p5514 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h47925 : (¬ p3146) ∨ (¬ p4118) ∨ (¬ p4196) ∨ (¬ p4228) ∨ (¬ p5514))
    : (¬ p4228) ∨ (¬ p5514) ∨ (¬ p4196) ∨ (¬ p3146) ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4228 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4196 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47925 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step102502 (p2406 p2505 p3238 p4053 p4717 p5514 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h42564 : (¬ p2505) ∨ (¬ p3238) ∨ (¬ p4053) ∨ (¬ p4717) ∨ (¬ p5514))
    : (¬ p4053) ∨ (¬ p5514) ∨ p2406 ∨ (¬ p2505) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4053 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42564 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step102503 (p2187 p3422 p3584 p3737 p3989 p5514 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h73502 : p3989 ∨ p2187)
    (h56054 : (¬ p3584) ∨ (¬ p3737) ∨ (¬ p3989) ∨ (¬ p5514))
    : (¬ p3737) ∨ (¬ p5514) ∨ p3422 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56054 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step102504 (p2946 p2950 p2955 : Prop)
    (h73331 : p2946 ∨ (¬ p2955))
    (h4034 : p2950 ∨ p2955)
    : p2950 ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2950) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2955) := (Or.elim h73331 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h4034 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102506 (p3425 p3959 p6062 : Prop)
    (h74407 : p3425 ∨ (¬ p6062))
    (h13381 : p3959 ∨ p6062)
    : p3959 ∨ p3425 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3959) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3425) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6062) := (Or.elim h74407 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13381 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102507 (p3399 p3545 p6044 : Prop)
    (h74383 : (¬ p3399) ∨ (¬ p6044))
    (h13263 : p3545 ∨ p6044)
    : p3545 ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3545) := (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6044) := (Or.elim h74383 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13263 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102508 (p2264 p4550 p5815 : Prop)
    (h74097 : p2264 ∨ (¬ p5815))
    (h11892 : p4550 ∨ p5815)
    : p4550 ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4550) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2264) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5815) := (Or.elim h74097 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11892 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102509 (p3178 p3755 p3767 p4035 p4461 p4790 p5284 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h53047 : (¬ p3178) ∨ (¬ p3767) ∨ (¬ p4035) ∨ (¬ p4461) ∨ (¬ p4790) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p3767) ∨ (¬ p4790) ∨ (¬ p3178) ∨ p3755 ∨ (¬ p4461) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3178 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h53047 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step102510 (p2958 p3755 p3767 p4035 p4207 p4790 p5284 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h61373 : (¬ p2958) ∨ (¬ p3767) ∨ (¬ p4035) ∨ (¬ p4207) ∨ (¬ p4790) ∨ (¬ p5284))
    : (¬ p5284) ∨ p3755 ∨ (¬ p4207) ∨ (¬ p3767) ∨ (¬ p4790) ∨ (¬ p2958) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4207 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h61373 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step102514 (p2449 p4658 p5860 : Prop)
    (h74157 : p2449 ∨ (¬ p5860))
    (h12155 : p4658 ∨ p5860)
    : p4658 ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4658) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5860) := (Or.elim h74157 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12155 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102515 (p3845 p3846 p3851 : Prop)
    (h73475 : (¬ p3845) ∨ (¬ p3851))
    (h5686 : p3846 ∨ p3851)
    : p3846 ∨ (¬ p3845) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3846) := (fun h => hn (Or.inl h));
    let u1 : p3845 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3851) := (Or.elim h73475 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h5686 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102516 (p2220 p4238 p5810 : Prop)
    (h74091 : (¬ p2220) ∨ (¬ p5810))
    (h11861 : p4238 ∨ p5810)
    : p4238 ∨ (¬ p2220) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4238) := (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5810) := (Or.elim h74091 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11861 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102517 (p3641 p5370 p6097 : Prop)
    (h74441 : p3641 ∨ (¬ p6097))
    (h13700 : p5370 ∨ p6097)
    : p5370 ∨ p3641 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5370) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3641) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6097) := (Or.elim h74441 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13700 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102518 (p2819 p4859 p5923 : Prop)
    (h74237 : p2819 ∨ (¬ p5923))
    (h12528 : p4859 ∨ p5923)
    : p4859 ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4859) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5923) := (Or.elim h74237 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12528 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102519 (p3389 p5197 p6040 : Prop)
    (h74377 : p3389 ∨ (¬ p6040))
    (h13238 : p5197 ∨ p6040)
    : p5197 ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5197) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6040) := (Or.elim h74377 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13238 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102520 (p2573 p2577 p2582 : Prop)
    (h73275 : p2573 ∨ (¬ p2582))
    (h3284 : p2577 ∨ p2582)
    : p2577 ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2577) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2582) := (Or.elim h73275 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h3284 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102521 (p2132 p2136 p2141 : Prop)
    (h73215 : p2132 ∨ (¬ p2141))
    (h2413 : p2136 ∨ p2141)
    : p2136 ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2136) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2141) := (Or.elim h73215 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h2413 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102523 (p3609 p5339 p6088 : Prop)
    (h74433 : p3609 ∨ (¬ p6088))
    (h13632 : p5339 ∨ p6088)
    : p5339 ∨ p3609 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5339) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6088) := (Or.elim h74433 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13632 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102524 (p3609 p5338 p6088 : Prop)
    (h74433 : p3609 ∨ (¬ p6088))
    (h13634 : p5338 ∨ p6088)
    : p5338 ∨ p3609 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5338) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6088) := (Or.elim h74433 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13634 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102525 (p3537 p4436 p6079 : Prop)
    (h74421 : p3537 ∨ (¬ p6079))
    (h13507 : p4436 ∨ p6079)
    : p4436 ∨ p3537 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4436) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3537) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6079) := (Or.elim h74421 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13507 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102527 (p2839 p4875 p5929 : Prop)
    (h74245 : p2839 ∨ (¬ p5929))
    (h12560 : p4875 ∨ p5929)
    : p4875 ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4875) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5929) := (Or.elim h74245 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12560 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102528 (p3641 p5369 p6097 : Prop)
    (h74441 : p3641 ∨ (¬ p6097))
    (h13697 : p5369 ∨ p6097)
    : p5369 ∨ p3641 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5369) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3641) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6097) := (Or.elim h74441 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13697 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102534 (p3286 p3291 p3295 : Prop)
    (h73379 : p3286 ∨ (¬ p3295))
    (h4707 : p3291 ∨ p3295)
    : p3291 ∨ p3286 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3291) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr h));
    let u2 : (¬ p3295) := (Or.elim h73379 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h4707 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102536 (p2177 p4133 p5797 : Prop)
    (h74073 : p2177 ∨ (¬ p5797))
    (h11787 : p4133 ∨ p5797)
    : p4133 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4133) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2177) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5797) := (Or.elim h74073 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11787 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102537 (p2619 p4744 p5888 : Prop)
    (h74191 : (¬ p2619) ∨ (¬ p5888))
    (h12315 : p4744 ∨ p5888)
    : p4744 ∨ (¬ p2619) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4744) := (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5888) := (Or.elim h74191 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12315 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102538 (p3323 p4190 p6067 : Prop)
    (h74409 : p3323 ∨ (¬ p6067))
    (h13423 : p4190 ∨ p6067)
    : p4190 ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4190) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6067) := (Or.elim h74409 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13423 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102539 (p3323 p5274 p6067 : Prop)
    (h74409 : p3323 ∨ (¬ p6067))
    (h13425 : p5274 ∨ p6067)
    : p5274 ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5274) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6067) := (Or.elim h74409 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13425 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102540 (p3323 p5276 p6067 : Prop)
    (h74409 : p3323 ∨ (¬ p6067))
    (h13427 : p5276 ∨ p6067)
    : p5276 ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5276) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6067) := (Or.elim h74409 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13427 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102541 (p3830 p4374 p6128 : Prop)
    (h74463 : (¬ p3830) ∨ (¬ p6128))
    (h14013 : p4374 ∨ p6128)
    : p4374 ∨ (¬ p3830) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4374) := (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6128) := (Or.elim h74463 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h14013 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102542 (p3654 p5379 p6100 : Prop)
    (h74445 : p3654 ∨ (¬ p6100))
    (h13729 : p5379 ∨ p6100)
    : p5379 ∨ p3654 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5379) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3654) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6100) := (Or.elim h74445 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13729 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102543 (p2668 p4771 p5896 : Prop)
    (h74201 : p2668 ∨ (¬ p5896))
    (h12364 : p4771 ∨ p5896)
    : p4771 ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4771) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2668) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5896) := (Or.elim h74201 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12364 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102544 (p3425 p5261 p6062 : Prop)
    (h74407 : p3425 ∨ (¬ p6062))
    (h13383 : p5261 ∨ p6062)
    : p5261 ∨ p3425 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5261) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3425) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6062) := (Or.elim h74407 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13383 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102546 (p3125 p4205 p5989 : Prop)
    (h74321 : p3125 ∨ (¬ p5989))
    (h12924 : p4205 ∨ p5989)
    : p4205 ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4205) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5989) := (Or.elim h74321 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12924 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102547 (p2982 p4953 p5957 : Prop)
    (h74283 : (¬ p2982) ∨ (¬ p5957))
    (h12728 : p4953 ∨ p5957)
    : p4953 ∨ (¬ p2982) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4953) := (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5957) := (Or.elim h74283 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12728 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102549 (p3093 p5021 p5981 : Prop)
    (h74311 : (¬ p3093) ∨ (¬ p5981))
    (h12877 : p5021 ∨ p5981)
    : p5021 ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5021) := (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5981) := (Or.elim h74311 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12877 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102550 (p2166 p4498 p5795 : Prop)
    (h74071 : (¬ p2166) ∨ (¬ p5795))
    (h11776 : p4498 ∨ p5795)
    : p4498 ∨ (¬ p2166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4498) := (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5795) := (Or.elim h74071 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11776 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102551 (p2098 p2103 p2107 : Prop)
    (h73205 : p2098 ∨ (¬ p2107))
    (h2343 : p2103 ∨ p2107)
    : p2103 ∨ p2098 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2103) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2107) := (Or.elim h73205 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h2343 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102553 (p2528 p4440 p5869 : Prop)
    (h74165 : p2528 ∨ (¬ p5869))
    (h12205 : p4440 ∨ p5869)
    : p4440 ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4440) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5869) := (Or.elim h74165 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12205 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102554 (p2437 p3579 p5858 : Prop)
    (h74155 : (¬ p2437) ∨ (¬ p5858))
    (h12140 : p3579 ∨ p5858)
    : p3579 ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3579) := (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5858) := (Or.elim h74155 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12140 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102555 (p2132 p2139 p2141 : Prop)
    (h73215 : p2132 ∨ (¬ p2141))
    (h2412 : p2139 ∨ p2141)
    : p2139 ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2139) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2141) := (Or.elim h73215 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h2412 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102556 (p2891 p4914 p5945 : Prop)
    (h74267 : (¬ p2891) ∨ (¬ p5945))
    (h12657 : p4914 ∨ p5945)
    : p4914 ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4914) := (fun h => hn (Or.inl h));
    let u1 : p2891 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5945) := (Or.elim h74267 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12657 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102557 (p2685 p4777 p5899 : Prop)
    (h74205 : p2685 ∨ (¬ p5899))
    (h12377 : p4777 ∨ p5899)
    : p4777 ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4777) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5899) := (Or.elim h74205 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12377 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102559 (p3389 p5199 p6040 : Prop)
    (h74377 : p3389 ∨ (¬ p6040))
    (h13239 : p5199 ∨ p6040)
    : p5199 ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5199) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6040) := (Or.elim h74377 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13239 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102560 (p3309 p5142 p6022 : Prop)
    (h74361 : p3309 ∨ (¬ p6022))
    (h13131 : p5142 ∨ p6022)
    : p5142 ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5142) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3309) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6022) := (Or.elim h74361 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13131 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102561 (p3073 p3440 p5974 : Prop)
    (h74301 : p3073 ∨ (¬ p5974))
    (h12836 : p3440 ∨ p5974)
    : p3440 ∨ p3073 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3440) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5974) := (Or.elim h74301 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12836 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102563 (p3246 p5102 p6010 : Prop)
    (h74345 : p3246 ∨ (¬ p6010))
    (h13056 : p5102 ∨ p6010)
    : p5102 ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5102) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6010) := (Or.elim h74345 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13056 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102564 (p2437 p4653 p5858 : Prop)
    (h74155 : (¬ p2437) ∨ (¬ p5858))
    (h12144 : p4653 ∨ p5858)
    : p4653 ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4653) := (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5858) := (Or.elim h74155 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12144 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102565 (p2727 p4810 p5911 : Prop)
    (h74221 : p2727 ∨ (¬ p5911))
    (h12450 : p4810 ∨ p5911)
    : p4810 ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4810) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5911) := (Or.elim h74221 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12450 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102571 (p3399 p5210 p6044 : Prop)
    (h74383 : (¬ p3399) ∨ (¬ p6044))
    (h13259 : p5210 ∨ p6044)
    : p5210 ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5210) := (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6044) := (Or.elim h74383 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13259 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102575 (p3449 p3858 p6056 : Prop)
    (h74399 : (¬ p3449) ∨ (¬ p6056))
    (h13340 : p3858 ∨ p6056)
    : p3858 ∨ (¬ p3449) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3858) := (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6056) := (Or.elim h74399 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13340 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102578 (p3115 p5038 p5987 : Prop)
    (h74319 : (¬ p3115) ∨ (¬ p5987))
    (h12912 : p5038 ∨ p5987)
    : p5038 ∨ (¬ p3115) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5038) := (fun h => hn (Or.inl h));
    let u1 : p3115 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5987) := (Or.elim h74319 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12912 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102581 (p2417 p4637 p5851 : Prop)
    (h74145 : p2417 ∨ (¬ p5851))
    (h12103 : p4637 ∨ p5851)
    : p4637 ∨ p2417 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4637) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5851) := (Or.elim h74145 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12103 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102583 (p2528 p4332 p5869 : Prop)
    (h74165 : p2528 ∨ (¬ p5869))
    (h12209 : p4332 ∨ p5869)
    : p4332 ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4332) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5869) := (Or.elim h74165 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12209 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102584 (p2493 p2501 p2502 : Prop)
    (h73261 : p2493 ∨ (¬ p2502))
    (h3131 : p2501 ∨ p2502)
    : p2501 ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2501) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2493) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2502) := (Or.elim h73261 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h3131 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102586 (p2829 p4870 p5927 : Prop)
    (h74243 : (¬ p2829) ∨ (¬ p5927))
    (h12549 : p4870 ∨ p5927)
    : p4870 ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4870) := (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5927) := (Or.elim h74243 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12549 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102587 (p2417 p4636 p5851 : Prop)
    (h74145 : p2417 ∨ (¬ p5851))
    (h12100 : p4636 ∨ p5851)
    : p4636 ∨ p2417 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4636) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5851) := (Or.elim h74145 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12100 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102591 (p2881 p4901 p5941 : Prop)
    (h74261 : p2881 ∨ (¬ p5941))
    (h12633 : p4901 ∨ p5941)
    : p4901 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4901) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5941) := (Or.elim h74261 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12633 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102592 (p3156 p5065 p5999 : Prop)
    (h74335 : (¬ p3156) ∨ (¬ p5999))
    (h12983 : p5065 ∨ p5999)
    : p5065 ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5065) := (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5999) := (Or.elim h74335 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12983 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102594 (p3564 p5321 p6082 : Prop)
    (h74425 : p3564 ∨ (¬ p6082))
    (h13546 : p5321 ∨ p6082)
    : p5321 ∨ p3564 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5321) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6082) := (Or.elim h74425 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13546 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102595 (p3564 p5322 p6082 : Prop)
    (h74425 : p3564 ∨ (¬ p6082))
    (h13547 : p5322 ∨ p6082)
    : p5322 ∨ p3564 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5322) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6082) := (Or.elim h74425 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13547 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102596 (p3276 p5131 p6020 : Prop)
    (h74359 : (¬ p3276) ∨ (¬ p6020))
    (h13114 : p5131 ∨ p6020)
    : p5131 ∨ (¬ p3276) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5131) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6020) := (Or.elim h74359 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13114 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102597 (p3016 p3379 p3452 p3574 p3807 p3901 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73422 : p3574 ∨ p3016)
    (h44697 : (¬ p3452) ∨ (¬ p3574) ∨ (¬ p3807) ∨ (¬ p3901))
    : (¬ p3807) ∨ (¬ p3901) ∨ p3379 ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3807 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44697 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step102605 (p2619 p4746 p5888 : Prop)
    (h74191 : (¬ p2619) ∨ (¬ p5888))
    (h12318 : p4746 ∨ p5888)
    : p4746 ∨ (¬ p2619) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4746) := (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5888) := (Or.elim h74191 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12318 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102606 (p2982 p4952 p5957 : Prop)
    (h74283 : (¬ p2982) ∨ (¬ p5957))
    (h12725 : p4952 ∨ p5957)
    : p4952 ∨ (¬ p2982) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4952) := (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5957) := (Or.elim h74283 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12725 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102607 (p4149 p5674 p6176 : Prop)
    (h74467 : (¬ p4149) ∨ (¬ p6176))
    (h15086 : p5674 ∨ p6176)
    : p5674 ∨ (¬ p4149) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5674) := (fun h => hn (Or.inl h));
    let u1 : p4149 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6176) := (Or.elim h74467 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h15086 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102611 (p3156 p4043 p5999 : Prop)
    (h74335 : (¬ p3156) ∨ (¬ p5999))
    (h12984 : p4043 ∨ p5999)
    : p4043 ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4043) := (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5999) := (Or.elim h74335 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12984 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102612 (p3755 p5454 p6121 : Prop)
    (h74457 : p3755 ∨ (¬ p6121))
    (h13913 : p5454 ∨ p6121)
    : p5454 ∨ p3755 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5454) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6121) := (Or.elim h74457 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13913 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102616 (p3537 p5312 p6079 : Prop)
    (h74421 : p3537 ∨ (¬ p6079))
    (h13504 : p5312 ∨ p6079)
    : p5312 ∨ p3537 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5312) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3537) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6079) := (Or.elim h74421 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13504 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102617 (p3537 p4353 p6079 : Prop)
    (h74421 : p3537 ∨ (¬ p6079))
    (h13506 : p4353 ∨ p6079)
    : p4353 ∨ p3537 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4353) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3537) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6079) := (Or.elim h74421 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13506 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102623 (p3434 p5229 p6052 : Prop)
    (h74393 : p3434 ∨ (¬ p6052))
    (h13310 : p5229 ∨ p6052)
    : p5229 ∨ p3434 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5229) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3434) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6052) := (Or.elim h74393 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13310 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102624 (p3434 p5228 p6052 : Prop)
    (h74393 : p3434 ∨ (¬ p6052))
    (h13312 : p5228 ∨ p6052)
    : p5228 ∨ p3434 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5228) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3434) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6052) := (Or.elim h74393 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13312 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102628 (p3830 p4439 p6128 : Prop)
    (h74463 : (¬ p3830) ∨ (¬ p6128))
    (h14014 : p4439 ∨ p6128)
    : p4439 ∨ (¬ p3830) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4439) := (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6128) := (Or.elim h74463 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h14014 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102632 (p3707 p5413 p6110 : Prop)
    (h74455 : (¬ p3707) ∨ (¬ p6110))
    (h13832 : p5413 ∨ p6110)
    : p5413 ∨ (¬ p3707) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5413) := (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6110) := (Or.elim h74455 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13832 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102633 (p3707 p5414 p6110 : Prop)
    (h74455 : (¬ p3707) ∨ (¬ p6110))
    (h13833 : p5414 ∨ p6110)
    : p5414 ∨ (¬ p3707) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5414) := (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6110) := (Or.elim h74455 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13833 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102636 (p3670 p5391 p6104 : Prop)
    (h74451 : (¬ p3670) ∨ (¬ p6104))
    (h13770 : p5391 ∨ p6104)
    : p5391 ∨ (¬ p3670) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5391) := (fun h => hn (Or.inl h));
    let u1 : p3670 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6104) := (Or.elim h74451 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13770 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102640 (p3654 p5378 p6100 : Prop)
    (h74445 : p3654 ∨ (¬ p6100))
    (h13728 : p5378 ∨ p6100)
    : p5378 ∨ p3654 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5378) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3654) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6100) := (Or.elim h74445 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13728 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102645 (p3516 p5294 p6073 : Prop)
    (h74413 : p3516 ∨ (¬ p6073))
    (h13466 : p5294 ∨ p6073)
    : p5294 ∨ p3516 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5294) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3516) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6073) := (Or.elim h74413 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13466 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102648 (p3516 p5295 p6073 : Prop)
    (h74413 : p3516 ∨ (¬ p6073))
    (h13470 : p5295 ∨ p6073)
    : p5295 ∨ p3516 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5295) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3516) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6073) := (Or.elim h74413 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13470 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102649 (p3425 p5260 p6062 : Prop)
    (h74407 : p3425 ∨ (¬ p6062))
    (h13379 : p5260 ∨ p6062)
    : p5260 ∨ p3425 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5260) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3425) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6062) := (Or.elim h74407 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13379 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102651 (p3343 p5175 p6032 : Prop)
    (h74371 : (¬ p3343) ∨ (¬ p6032))
    (h13185 : p5175 ∨ p6032)
    : p5175 ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5175) := (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6032) := (Or.elim h74371 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13185 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102652 (p3343 p5177 p6032 : Prop)
    (h74371 : (¬ p3343) ∨ (¬ p6032))
    (h13188 : p5177 ∨ p6032)
    : p5177 ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5177) := (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6032) := (Or.elim h74371 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13188 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102655 (p3276 p4184 p6020 : Prop)
    (h74359 : (¬ p3276) ∨ (¬ p6020))
    (h13115 : p4184 ∨ p6020)
    : p4184 ∨ (¬ p3276) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4184) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6020) := (Or.elim h74359 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13115 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102657 (p3276 p5133 p6020 : Prop)
    (h74359 : (¬ p3276) ∨ (¬ p6020))
    (h13118 : p5133 ∨ p6020)
    : p5133 ∨ (¬ p3276) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5133) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6020) := (Or.elim h74359 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13118 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102658 (p3266 p5121 p6017 : Prop)
    (h74355 : (¬ p3266) ∨ (¬ p6017))
    (h13097 : p5121 ∨ p6017)
    : p5121 ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5121) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6017) := (Or.elim h74355 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13097 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102660 (p3256 p5109 p6013 : Prop)
    (h74349 : p3256 ∨ (¬ p6013))
    (h13077 : p5109 ∨ p6013)
    : p5109 ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5109) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6013) := (Or.elim h74349 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13077 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102661 (p3201 p5082 p6004 : Prop)
    (h74341 : p3201 ∨ (¬ p6004))
    (h13017 : p5082 ∨ p6004)
    : p5082 ∨ p3201 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5082) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6004) := (Or.elim h74341 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13017 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102664 (p3146 p5056 p5995 : Prop)
    (h74329 : p3146 ∨ (¬ p5995))
    (h12960 : p5056 ∨ p5995)
    : p5056 ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5056) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5995) := (Or.elim h74329 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12960 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102665 (p3115 p4039 p5987 : Prop)
    (h74319 : (¬ p3115) ∨ (¬ p5987))
    (h12911 : p4039 ∨ p5987)
    : p4039 ∨ (¬ p3115) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4039) := (fun h => hn (Or.inl h));
    let u1 : p3115 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5987) := (Or.elim h74319 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12911 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102666 (p3115 p5039 p5987 : Prop)
    (h74319 : (¬ p3115) ∨ (¬ p5987))
    (h12914 : p5039 ∨ p5987)
    : p5039 ∨ (¬ p3115) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5039) := (fun h => hn (Or.inl h));
    let u1 : p3115 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5987) := (Or.elim h74319 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12914 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102668 (p3105 p5030 p5984 : Prop)
    (h74315 : (¬ p3105) ∨ (¬ p5984))
    (h12893 : p5030 ∨ p5984)
    : p5030 ∨ (¬ p3105) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5030) := (fun h => hn (Or.inl h));
    let u1 : p3105 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5984) := (Or.elim h74315 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12893 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102669 (p3105 p5031 p5984 : Prop)
    (h74315 : (¬ p3105) ∨ (¬ p5984))
    (h12894 : p5031 ∨ p5984)
    : p5031 ∨ (¬ p3105) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5031) := (fun h => hn (Or.inl h));
    let u1 : p3105 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5984) := (Or.elim h74315 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12894 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102672 (p3073 p3438 p5974 : Prop)
    (h74301 : p3073 ∨ (¬ p5974))
    (h12834 : p3438 ∨ p5974)
    : p3438 ∨ p3073 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3438) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5974) := (Or.elim h74301 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12834 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102677 (p2972 p4387 p5954 : Prop)
    (h74279 : (¬ p2972) ∨ (¬ p5954))
    (h12707 : p4387 ∨ p5954)
    : p4387 ∨ (¬ p2972) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4387) := (fun h => hn (Or.inl h));
    let u1 : p2972 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5954) := (Or.elim h74279 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12707 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102680 (p2901 p4919 p5948 : Prop)
    (h74271 : (¬ p2901) ∨ (¬ p5948))
    (h12673 : p4919 ∨ p5948)
    : p4919 ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4919) := (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5948) := (Or.elim h74271 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12673 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102683 (p2761 p4828 p5915 : Prop)
    (h74227 : (¬ p2761) ∨ (¬ p5915))
    (h12471 : p4828 ∨ p5915)
    : p4828 ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4828) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5915) := (Or.elim h74227 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12471 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102684 (p2761 p4830 p5915 : Prop)
    (h74227 : (¬ p2761) ∨ (¬ p5915))
    (h12474 : p4830 ∨ p5915)
    : p4830 ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4830) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5915) := (Or.elim h74227 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12474 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102685 (p2707 p4797 p5906 : Prop)
    (h74215 : (¬ p2707) ∨ (¬ p5906))
    (h12419 : p4797 ∨ p5906)
    : p4797 ∨ (¬ p2707) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4797) := (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5906) := (Or.elim h74215 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12419 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102691 (p2383 p4614 p5842 : Prop)
    (h74133 : p2383 ∨ (¬ p5842))
    (h12050 : p4614 ∨ p5842)
    : p4614 ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4614) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2383) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5842) := (Or.elim h74133 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12050 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102693 (p2341 p4588 p5830 : Prop)
    (h74117 : p2341 ∨ (¬ p5830))
    (h11978 : p4588 ∨ p5830)
    : p4588 ∨ p2341 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4588) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5830) := (Or.elim h74117 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11978 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102694 (p2331 p4580 p5827 : Prop)
    (h74113 : p2331 ∨ (¬ p5827))
    (h11960 : p4580 ∨ p5827)
    : p4580 ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4580) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5827) := (Or.elim h74113 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11960 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102696 (p2295 p4569 p5824 : Prop)
    (h74109 : p2295 ∨ (¬ p5824))
    (h11943 : p4569 ∨ p5824)
    : p4569 ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4569) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5824) := (Or.elim h74109 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11943 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102703 (p2122 p4472 p5788 : Prop)
    (h74061 : p2122 ∨ (¬ p5788))
    (h11734 : p4472 ∨ p5788)
    : p4472 ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4472) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5788) := (Or.elim h74061 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11734 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102704 (p2088 p4456 p5785 : Prop)
    (h74057 : p2088 ∨ (¬ p5785))
    (h11714 : p4456 ∨ p5785)
    : p4456 ∨ p2088 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4456) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2088) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5785) := (Or.elim h74057 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11714 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102705 (p2088 p4455 p5785 : Prop)
    (h74057 : p2088 ∨ (¬ p5785))
    (h11715 : p4455 ∨ p5785)
    : p4455 ∨ p2088 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4455) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2088) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5785) := (Or.elim h74057 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11715 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102792 (p3845 p3847 p3851 : Prop)
    (h73475 : (¬ p3845) ∨ (¬ p3851))
    (h5685 : p3847 ∨ p3851)
    : p3847 ∨ (¬ p3845) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3847) := (fun h => hn (Or.inl h));
    let u1 : p3845 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3851) := (Or.elim h73475 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h5685 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102798 (p3811 p3816 p5481 : Prop)
    (h73465 : (¬ p3811) ∨ (¬ p3816))
    (h9508 : (¬ p3811) ∨ p3816 ∨ p5481)
    : (¬ p3811) ∨ p5481 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3811 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5481) := (fun h => hn (Or.inr h));
    let u2 : (¬ p3816) := (Or.elim h73465 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    (Or.elim h9508 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step102803 (p3804 p3810 p5480 : Prop)
    (h73463 : (¬ p3804) ∨ (¬ p3810))
    (h9504 : (¬ p3804) ∨ p3810 ∨ p5480)
    : (¬ p3804) ∨ p5480 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3804 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5480) := (fun h => hn (Or.inr h));
    let u2 : (¬ p3810) := (Or.elim h73463 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    (Or.elim h9504 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (u1 r1)))))))

theorem step102812 (p3193 p3229 p3230 : Prop)
    (h73367 : (¬ p3193) ∨ (¬ p3230))
    (h4576 : p3229 ∨ p3230)
    : p3229 ∨ (¬ p3193) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3229) := (fun h => hn (Or.inl h));
    let u1 : p3193 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3230) := (Or.elim h73367 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h4576 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102813 (p3193 p3226 p3230 : Prop)
    (h73367 : (¬ p3193) ∨ (¬ p3230))
    (h4579 : p3226 ∨ p3230)
    : p3226 ∨ (¬ p3193) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3226) := (fun h => hn (Or.inl h));
    let u1 : p3193 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3230) := (Or.elim h73367 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h4579 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102816 (p2996 p3034 p3035 : Prop)
    (h73343 : (¬ p2996) ∨ (¬ p3035))
    (h4189 : p3034 ∨ p3035)
    : p3034 ∨ (¬ p2996) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3034) := (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3035) := (Or.elim h73343 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h4189 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102822 (p2470 p2478 p2479 : Prop)
    (h73251 : p2470 ∨ (¬ p2479))
    (h3083 : p2478 ∨ p2479)
    : p2478 ∨ p2470 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2478) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2470) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2479) := (Or.elim h73251 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h3083 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102827 (p2098 p2102 p2107 : Prop)
    (h73205 : p2098 ∨ (¬ p2107))
    (h2346 : p2102 ∨ p2107)
    : p2102 ∨ p2098 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2102) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2107) := (Or.elim h73205 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h2346 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step102828 (p2192 p2284 p2727 p3952 p4111 p4173 p4704 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73496 : p3952 ∨ p2284)
    (h73527 : (¬ p2192) ∨ (¬ p4173))
    (h73046 : p4704)
    (h67933 : p4173 ∨ (¬ p3952) ∨ (¬ p4704) ∨ (¬ p4111))
    : p2727 ∨ p2284 ∨ (¬ p2192) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : (¬ p4173) := (Or.elim h73527 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    let u6 : p4704 := h73046;
    (Or.elim h67933 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step102837 (p2230 p2274 p2553 p2589 p3097 p3389 p4709 p4718 : Prop)
    (h73718 : p4709 ∨ (¬ p2553))
    (h73352 : p3097 ∨ p2274)
    (h73284 : p2589 ∨ p2230)
    (h67551 : (¬ p4709) ∨ (¬ p3097) ∨ (¬ p3389) ∨ (¬ p4718) ∨ (¬ p2589))
    : (¬ p2553) ∨ p2274 ∨ (¬ p3389) ∨ (¬ p4718) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4709 := (Or.elim h73718 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h67551 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step102838 (p2177 p2295 p2881 p3568 : Prop)
    (h73415 : (¬ p2295) ∨ (¬ p3568))
    (h67448 : p2881 ∨ p3568 ∨ (¬ p2177))
    : (¬ p2295) ∨ p2881 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3568) := (Or.elim h73415 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    (Or.elim h67448 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step102840 (p2440 p2542 p2630 p2651 p2797 p4195 p4389 p4715 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73270 : p2542 ∨ p2440)
    (h67793 : (¬ p2542) ∨ (¬ p4715) ∨ (¬ p4389) ∨ (¬ p2630) ∨ (¬ p4195) ∨ (¬ p2651))
    : (¬ p2651) ∨ p2797 ∨ p2440 ∨ (¬ p2630) ∨ (¬ p4389) ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h67793 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step102841 (p2274 p2307 p2493 p2578 p2630 p2696 p3097 p4194 p4389 p4814 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h67534 : (¬ p2493) ∨ (¬ p2630) ∨ (¬ p4389) ∨ (¬ p4194) ∨ (¬ p2578) ∨ (¬ p3097) ∨ (¬ p4814) ∨ (¬ p2696) ∨ (¬ p2307))
    : (¬ p2307) ∨ p2274 ∨ (¬ p2493) ∨ (¬ p2696) ∨ (¬ p2578) ∨ (¬ p2630) ∨ (¬ p4389) ∨ (¬ p4814) ∨ (¬ p4194) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h67534 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step102842 (p2132 p2177 p2274 p2299 p2459 p2881 p3609 p4509 p4557 p4665 p4903 : Prop)
    (h73820 : p4903 ∨ (¬ p2881))
    (h73234 : p2299 ∨ p2177)
    (h73696 : p4665 ∨ p2459)
    (h73636 : p4557 ∨ (¬ p2274))
    (h68257 : (¬ p4903) ∨ (¬ p4509) ∨ (¬ p4665) ∨ (¬ p2299) ∨ (¬ p4557) ∨ (¬ p2132) ∨ (¬ p3609))
    : (¬ p2881) ∨ p2177 ∨ (¬ p3609) ∨ (¬ p2132) ∨ p2459 ∨ (¬ p4509) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2177) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4903 := (Or.elim h73820 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u8 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4665 := (Or.elim h73696 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u6))));
    (Or.elim h68257 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step102843 (p2132 p2630 p2696 p2810 p3365 p4704 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h73316 : p2810 ∨ p2630)
    (h73046 : p4704)
    (h67974 : (¬ p3365) ∨ (¬ p2810) ∨ (¬ p4704) ∨ (¬ p2132))
    : (¬ p2132) ∨ p2696 ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4704 := h73046;
    (Or.elim h67974 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step102848 (p2829 p3016 p3367 p3574 p3585 p4753 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73428 : p3585 ∨ p3367)
    (h67852 : (¬ p2829) ∨ (¬ p3585) ∨ (¬ p3574) ∨ (¬ p4753))
    : (¬ p2829) ∨ p3016 ∨ p3367 ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h67852 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step102850 (p2187 p2829 p3537 p4242 p4889 : Prop)
    (h73538 : p4242 ∨ p3537)
    (h67881 : (¬ p4242) ∨ (¬ p2829) ∨ (¬ p2187) ∨ (¬ p4889))
    : p3537 ∨ (¬ p2829) ∨ (¬ p2187) ∨ (¬ p4889) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3537) := (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4889 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4242 := (Or.elim h73538 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h67881 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step102851 (p2122 p2177 p2737 p2743 p2829 p4328 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h67839 : (¬ p2829) ∨ (¬ p4328) ∨ (¬ p2177) ∨ (¬ p2743) ∨ (¬ p2122))
    : (¬ p2829) ∨ (¬ p2122) ∨ p2737 ∨ (¬ p4328) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h67839 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step102852 (p2230 p2598 p2774 p2829 p4728 : Prop)
    (h73730 : p4728 ∨ (¬ p2598))
    (h67931 : p2774 ∨ (¬ p2829) ∨ (¬ p2230) ∨ (¬ p4728))
    : p2774 ∨ (¬ p2829) ∨ (¬ p2230) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4728 := (Or.elim h73730 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h67931 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step102853 (p2122 p2608 p2630 p2737 p2797 p2810 p4844 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73788 : p4844 ∨ (¬ p2797))
    (h67869 : (¬ p4844) ∨ (¬ p2737) ∨ (¬ p2810) ∨ (¬ p2608) ∨ (¬ p2122))
    : (¬ p2122) ∨ (¬ p2608) ∨ p2630 ∨ (¬ p2737) ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4844 := (Or.elim h73788 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    (Or.elim h67869 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step102854 (p2098 p2696 p2737 p3365 p3609 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h68206 : (¬ p3365) ∨ (¬ p2737) ∨ (¬ p3609) ∨ (¬ p2098))
    : (¬ p2098) ∨ p2696 ∨ (¬ p3609) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h68206 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step102856 (p2230 p2839 p2850 p3362 p3583 p3684 p3698 p4730 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73424 : p3583 ∨ p2839)
    (h72320 : (¬ p3362) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p4730) ∨ (¬ p3684) ∨ (¬ p2230))
    : (¬ p3698) ∨ p2850 ∨ p2839 ∨ (¬ p4730) ∨ (¬ p2230) ∨ (¬ p3362) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3698 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h72320 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step102857 (p2210 p2230 p2608 p2850 p3367 p3684 p3954 p5215 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73962 : p5215 ∨ (¬ p3367))
    (h73498 : p3954 ∨ p2608)
    (h68094 : (¬ p2230) ∨ (¬ p2210) ∨ (¬ p3684) ∨ (¬ p5215) ∨ (¬ p3954))
    : p2850 ∨ (¬ p3367) ∨ p2608 ∨ (¬ p2230) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p5215 := (Or.elim h73962 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u7 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h68094 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step102858 (p2210 p2230 p2850 p3379 p3684 p5189 p5217 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73948 : p5189 ∨ p3379)
    (h68093 : (¬ p5189) ∨ (¬ p2230) ∨ (¬ p2210) ∨ (¬ p3684) ∨ (¬ p5217))
    : p2850 ∨ (¬ p2230) ∨ (¬ p5217) ∨ p3379 ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5217 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p5189 := (Or.elim h73948 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h68093 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step102859 (p2210 p2241 p2251 p2608 p2651 p2657 p2750 p2946 p2952 p3555 p3954 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73412 : p3555 ∨ p2210)
    (h73287 : (¬ p2651) ∨ (¬ p2657))
    (h73498 : p3954 ∨ p2608)
    (h73230 : p2251 ∨ (¬ p2241))
    (h67516 : (¬ p2251) ∨ (¬ p3555) ∨ (¬ p2952) ∨ p2657 ∨ (¬ p2750) ∨ (¬ p3954))
    : p2946 ∨ p2210 ∨ (¬ p2651) ∨ p2608 ∨ (¬ p2241) ∨ (¬ p2750) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : (¬ p2657) := (Or.elim h73287 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    let u9 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2251 := (Or.elim h73230 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    (Or.elim h67516 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u9)))))))))))))

theorem step102861 (p2881 p3246 p3609 p3690 p4807 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h67759 : (¬ p3690) ∨ (¬ p4807) ∨ (¬ p2881) ∨ (¬ p3609))
    : p3246 ∨ (¬ p4807) ∨ (¬ p3609) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p4807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h67759 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step102864 (p2427 p2891 p3051 p3201 p3876 p4643 p4730 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73684 : p4643 ∨ p2427)
    (h67403 : (¬ p4643) ∨ (¬ p2891) ∨ (¬ p3876) ∨ (¬ p4730) ∨ (¬ p3051))
    : (¬ p2891) ∨ p3201 ∨ (¬ p3051) ∨ (¬ p4730) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4643 := (Or.elim h73684 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h67403 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step102866 (p2190 p2220 p2563 p2641 p2651 p2727 p3016 p4120 p4154 p4716 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73722 : p4716 ∨ (¬ p2563))
    (h73522 : p4120 ∨ p2220)
    (h67774 : (¬ p4716) ∨ (¬ p4154) ∨ p3016 ∨ (¬ p2651) ∨ (¬ p4120) ∨ (¬ p2190) ∨ (¬ p2727))
    : p2641 ∨ (¬ p2190) ∨ (¬ p2563) ∨ (¬ p2727) ∨ p2220 ∨ (¬ p2651) ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p4716 := (Or.elim h73722 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u9 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h67774 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step102867 (p2156 p2563 p2651 p2946 p2949 p3646 : Prop)
    (h73328 : p2949 ∨ p2946)
    (h73436 : p3646 ∨ p2156)
    (h69710 : (¬ p3646) ∨ (¬ p2949) ∨ (¬ p2651) ∨ (¬ p2563))
    : p2946 ∨ p2156 ∨ (¬ p2563) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2949 := (Or.elim h73328 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h69710 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step102868 (p2608 p2651 p2727 p2750 p3954 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73498 : p3954 ∨ p2608)
    (h68054 : (¬ p2651) ∨ (¬ p4111) ∨ (¬ p2750) ∨ (¬ p3954))
    : p2727 ∨ p2608 ∨ (¬ p2651) ∨ (¬ p2750) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h68054 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step102869 (p2331 p2440 p2542 p2651 p4715 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h67886 : (¬ p2651) ∨ p2331 ∨ (¬ p2542) ∨ (¬ p4715))
    : p2331 ∨ (¬ p2651) ∨ (¬ p4715) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h67886 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step102871 (p2088 p2132 p2210 p2230 p2274 p2284 p2307 p2459 p2563 p2619 p2651 p2663 p2696 p2839 p3097 p3146 p3955 p3988 p4433 p4489 p4788 p4814 p4902 p5055 : Prop)
    (h73896 : p5055 ∨ p3146)
    (h73760 : p4788 ∨ (¬ p2696))
    (h73352 : p3097 ∨ p2274)
    (h67624 : (¬ p5055) ∨ (¬ p2284) ∨ (¬ p2651) ∨ (¬ p2663) ∨ (¬ p2230) ∨ (¬ p2619) ∨ (¬ p2563) ∨ (¬ p3988) ∨ (¬ p3097) ∨ (¬ p4814) ∨ (¬ p4433) ∨ (¬ p4902) ∨ (¬ p2459) ∨ (¬ p4788) ∨ p2210 ∨ (¬ p2839) ∨ (¬ p3955) ∨ (¬ p2307) ∨ (¬ p4489) ∨ (¬ p2132) ∨ (¬ p2088))
    : (¬ p2307) ∨ p2210 ∨ (¬ p2663) ∨ (¬ p3955) ∨ (¬ p4902) ∨ p3146 ∨ (¬ p2839) ∨ (¬ p2696) ∨ (¬ p2230) ∨ (¬ p2132) ∨ (¬ p4433) ∨ p2274 ∨ (¬ p4814) ∨ (¬ p2088) ∨ (¬ p3988) ∨ (¬ p2284) ∨ (¬ p2459) ∨ (¬ p2651) ∨ (¬ p2619) ∨ (¬ p4489) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))));
    let u19 : p4489 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))));
    let u20 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))))))));
    let u21 : p5055 := (Or.elim h73896 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u22 : p4788 := (Or.elim h73760 (fun q0 => q0) (fun r0 => (False.elim (r0 u7))));
    let u23 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    (Or.elim h67624 (fun q0 => (False.elim (q0 u21))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u15))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u17))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u18))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u20))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u14))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u23))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u10))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u4))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u16))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u22))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (u1 q14))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u6))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u3))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u0))) (fun r17 => (Or.elim r17 (fun q18 => (False.elim (q18 u19))) (fun r18 => (Or.elim r18 (fun q19 => (False.elim (q19 u9))) (fun r19 => (False.elim (r19 u13)))))))))))))))))))))))))))))))))))))))))))

theorem step102872 (p2598 p2630 p2651 p3055 p4748 : Prop)
    (h73740 : p4748 ∨ p2630)
    (h73350 : p3055 ∨ p2598)
    (h67393 : (¬ p4748) ∨ (¬ p3055) ∨ (¬ p2651))
    : p2630 ∨ (¬ p2651) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4748 := (Or.elim h73740 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h67393 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u1)))))))

theorem step102873 (p2230 p2651 p2661 p2946 p2949 p4537 : Prop)
    (h73328 : p2949 ∨ p2946)
    (h73624 : p4537 ∨ (¬ p2230))
    (h73292 : p2661 ∨ (¬ p2651))
    (h67499 : (¬ p2661) ∨ (¬ p4537) ∨ (¬ p2949))
    : p2946 ∨ (¬ p2230) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2949 := (Or.elim h73328 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p4537 := (Or.elim h73624 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u5 : p2661 := (Or.elim h73292 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h67499 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u3)))))))

theorem step102874 (p2230 p2589 p2651 p2661 p2946 p2952 p3389 p4646 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73292 : p2661 ∨ (¬ p2651))
    (h73284 : p2589 ∨ p2230)
    (h67497 : (¬ p2661) ∨ (¬ p3389) ∨ (¬ p4646) ∨ (¬ p2589) ∨ (¬ p2952))
    : p2946 ∨ (¬ p3389) ∨ (¬ p2651) ∨ p2230 ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2661 := (Or.elim h73292 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h67497 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step102883 (p2187 p2331 p2668 p2797 p3136 p3324 p4195 p4582 p4790 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73650 : p4582 ∨ (¬ p2331))
    (h73386 : p3324 ∨ p2668)
    (h67716 : (¬ p4195) ∨ (¬ p2187) ∨ (¬ p3324) ∨ (¬ p3136) ∨ (¬ p4582) ∨ (¬ p4790))
    : p2797 ∨ (¬ p2331) ∨ p2668 ∨ (¬ p3136) ∨ (¬ p2187) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4582 := (Or.elim h73650 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u8 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h67716 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step102884 (p2192 p2249 p2284 p2331 p2963 p3745 p3952 p4365 p4960 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73496 : p3952 ∨ p2284)
    (h67660 : (¬ p2192) ∨ (¬ p2963) ∨ (¬ p3952) ∨ (¬ p3745) ∨ (¬ p4960) ∨ (¬ p4365) ∨ (¬ p2249))
    : (¬ p4365) ∨ p2331 ∨ (¬ p3745) ∨ (¬ p4960) ∨ p2284 ∨ (¬ p2192) ∨ (¬ p2249) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4365 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h67660 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step102887 (p2363 p2406 p2440 p2510 p3016 p3073 p3238 p3487 p4347 p4610 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73374 : p3238 ∨ p2406)
    (h67608 : (¬ p3016) ∨ (¬ p3238) ∨ (¬ p2440) ∨ (¬ p2510) ∨ (¬ p4347) ∨ (¬ p4610) ∨ (¬ p3487) ∨ (¬ p3073))
    : (¬ p3073) ∨ p2363 ∨ (¬ p3487) ∨ (¬ p4610) ∨ (¬ p2440) ∨ (¬ p2510) ∨ p2406 ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4610 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2510 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h67608 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step102889 (p2088 p2459 p2881 p3570 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73418 : p3570 ∨ p2881)
    (h68274 : (¬ p3570) ∨ (¬ p4348) ∨ (¬ p2088))
    : p2459 ∨ p2881 ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h68274 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step102890 (p2098 p2241 p2247 p2608 p3537 p4242 p4735 : Prop)
    (h73538 : p4242 ∨ p3537)
    (h73226 : p2247 ∨ p2241)
    (h73734 : p4735 ∨ (¬ p2608))
    (h67772 : (¬ p2247) ∨ (¬ p4242) ∨ (¬ p4735) ∨ (¬ p2098))
    : p3537 ∨ p2241 ∨ (¬ p2098) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3537) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4242 := (Or.elim h73538 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4735 := (Or.elim h73734 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h67772 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step102891 (p2241 p2247 p2608 p2696 p3589 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h67786 : (¬ p2247) ∨ (¬ p2608) ∨ (¬ p3589) ∨ (¬ p2696))
    : p2241 ∨ (¬ p2608) ∨ (¬ p2696) ∨ (¬ p3589) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h67786 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step102894 (p2187 p2274 p2668 p3166 p3989 p4560 p4772 : Prop)
    (h73752 : p4772 ∨ (¬ p2668))
    (h72955 : p4560)
    (h73502 : p3989 ∨ p2187)
    (h67495 : (¬ p4772) ∨ (¬ p3166) ∨ (¬ p3989) ∨ (¬ p2274) ∨ (¬ p4560))
    : (¬ p2668) ∨ (¬ p2274) ∨ (¬ p3166) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4772 := (Or.elim h73752 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u5 : p4560 := h72955;
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h67495 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step102895 (p2651 p2657 p2946 p2952 p3083 p4256 p4608 : Prop)
    (h73329 : (¬ p2946) ∨ (¬ p2952))
    (h73542 : p4256 ∨ p3083)
    (h73288 : p2657 ∨ p2651)
    (h67669 : p2952 ∨ (¬ p4256) ∨ (¬ p4608) ∨ (¬ p2657))
    : (¬ p2946) ∨ p3083 ∨ (¬ p4608) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2952) := (Or.elim h73329 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u5 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h67669 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step102896 (p2440 p2850 p2946 p2952 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h67447 : (¬ p2440) ∨ (¬ p2952) ∨ (¬ p2850))
    : (¬ p2850) ∨ p2946 ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h67447 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u0)))))))

theorem step102898 (p2437 p2717 p2850 p2881 p3201 p3659 p4750 p5081 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h73912 : p5081 ∨ p3201)
    (h67951 : (¬ p5081) ∨ (¬ p3659) ∨ (¬ p2437) ∨ (¬ p2850) ∨ (¬ p4750) ∨ (¬ p2881))
    : p2717 ∨ (¬ p2881) ∨ (¬ p2437) ∨ p3201 ∨ (¬ p4750) ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p5081 := (Or.elim h73912 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h67951 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step102899 (p2807 p2946 p2956 p3051 p3414 : Prop)
    (h73334 : p2956 ∨ (¬ p2946))
    (h73392 : p3414 ∨ p2807)
    (h67401 : (¬ p3414) ∨ (¬ p2956) ∨ (¬ p3051))
    : (¬ p3051) ∨ (¬ p2946) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2956 := (Or.elim h73334 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u4 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h67401 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u0)))))))

theorem step102900 (p2331 p2563 p2946 p2963 p4702 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h67395 : (¬ p2946) ∨ (¬ p4702) ∨ (¬ p2563) ∨ p2331 ∨ (¬ p2963))
    : (¬ p2946) ∨ p2331 ∨ (¬ p2563) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h67395 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step102901 (p2210 p2241 p2251 p2608 p2750 p2946 p3555 p3954 : Prop)
    (h73230 : p2251 ∨ (¬ p2241))
    (h73412 : p3555 ∨ p2210)
    (h73498 : p3954 ∨ p2608)
    (h67574 : (¬ p2251) ∨ (¬ p2946) ∨ (¬ p2750) ∨ (¬ p3555) ∨ (¬ p3954))
    : (¬ p2241) ∨ p2210 ∨ (¬ p2750) ∨ p2608 ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2251 := (Or.elim h73230 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u6 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h67574 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step102902 (p2230 p2563 p2589 p2651 p2654 p2946 p4110 : Prop)
    (h73286 : p2654 ∨ p2651)
    (h73284 : p2589 ∨ p2230)
    (h73516 : p4110 ∨ p2563)
    (h67425 : (¬ p2654) ∨ (¬ p2589) ∨ (¬ p2946) ∨ (¬ p4110))
    : p2651 ∨ (¬ p2946) ∨ p2230 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2654 := (Or.elim h73286 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h67425 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step102904 (p2230 p2373 p2440 p2528 p2850 p3156 p3362 p3422 p3584 p3693 p3880 p4703 p4715 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h73714 : p4703 ∨ p2440)
    (h73490 : p3880 ∨ p2373)
    (h68084 : (¬ p3156) ∨ (¬ p3880) ∨ (¬ p3693) ∨ (¬ p2850) ∨ (¬ p2230) ∨ (¬ p3584) ∨ (¬ p2528) ∨ (¬ p3362) ∨ (¬ p4703) ∨ (¬ p4715))
    : (¬ p3156) ∨ (¬ p2528) ∨ p3422 ∨ (¬ p2230) ∨ (¬ p3693) ∨ (¬ p2850) ∨ p2440 ∨ p2373 ∨ (¬ p4715) ∨ (¬ p3362) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p4703 := (Or.elim h73714 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h68084 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step102905 (p2177 p2246 p2295 p2331 p2608 p2641 p2737 p2747 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73302 : p2747 ∨ (¬ p2737))
    (h67428 : (¬ p2747) ∨ (¬ p2608) ∨ (¬ p2177) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p4154) ∨ p2246)
    : p2246 ∨ p2641 ∨ (¬ p2177) ∨ (¬ p2608) ∨ (¬ p2331) ∨ (¬ p2737) ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2246) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p2747 := (Or.elim h73302 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    (Or.elim h67428 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (False.elim (u0 r5)))))))))))))))

theorem step102910 (p2122 p2177 p2363 p2774 p4502 : Prop)
    (h73604 : p4502 ∨ (¬ p2177))
    (h67990 : (¬ p2774) ∨ (¬ p4502) ∨ (¬ p2363) ∨ (¬ p2122))
    : (¬ p2122) ∨ (¬ p2774) ∨ (¬ p2363) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4502 := (Or.elim h73604 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h67990 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step102911 (p2132 p2156 p2563 p2598 p3055 p4110 p4392 p4749 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h73350 : p3055 ∨ p2598)
    (h68213 : (¬ p3055) ∨ (¬ p4392) ∨ (¬ p4749) ∨ (¬ p2156) ∨ (¬ p4110) ∨ (¬ p2132))
    : (¬ p4392) ∨ (¬ p2132) ∨ (¬ p2156) ∨ p2563 ∨ (¬ p4749) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4392 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h68213 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step102919 (p2427 p2493 p2499 p2891 p4235 p4715 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73260 : p2499 ∨ p2493)
    (h67749 : (¬ p2891) ∨ (¬ p2499) ∨ (¬ p4235) ∨ (¬ p4715))
    : (¬ p2891) ∨ p2427 ∨ p2493 ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h67749 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step102922 (p2166 p2191 p2341 p2881 p4525 p4900 p4988 : Prop)
    (h73818 : p4900 ∨ p2881)
    (h73222 : p2191 ∨ p2166)
    (h68273 : (¬ p4988) ∨ (¬ p2191) ∨ (¬ p4900) ∨ (¬ p2341) ∨ (¬ p4525))
    : (¬ p4988) ∨ (¬ p2341) ∨ (¬ p4525) ∨ p2881 ∨ p2166 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4988 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4525 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4900 := (Or.elim h73818 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p2191 := (Or.elim h73222 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h68273 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step102925 (p2156 p2210 p2241 p2563 p2750 p3369 p3371 p3555 p3646 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73436 : p3646 ∨ p2156)
    (h68033 : (¬ p2241) ∨ (¬ p3555) ∨ (¬ p2750) ∨ (¬ p3371) ∨ (¬ p3369) ∨ (¬ p2563) ∨ (¬ p3646))
    : (¬ p2563) ∨ p2210 ∨ p2156 ∨ (¬ p3371) ∨ (¬ p3369) ∨ (¬ p2750) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3369 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h68033 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (r5 u8)))))))))))))))

theorem step102928 (p2284 p2363 p2383 p2727 p2891 p2992 p3743 p4111 p4558 p4562 p4704 p4958 : Prop)
    (h73638 : p4562 ∨ p2284)
    (h73852 : p4958 ∨ (¬ p2992))
    (h73046 : p4704)
    (h73518 : p4111 ∨ p2727)
    (h67929 : (¬ p4958) ∨ (¬ p2891) ∨ (¬ p2383) ∨ (¬ p4562) ∨ (¬ p2363) ∨ (¬ p4704) ∨ (¬ p4111) ∨ (¬ p4558) ∨ (¬ p3743))
    : (¬ p2383) ∨ (¬ p3743) ∨ (¬ p2363) ∨ p2284 ∨ (¬ p2992) ∨ (¬ p4558) ∨ (¬ p2891) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4562 := (Or.elim h73638 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p4958 := (Or.elim h73852 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u10 : p4704 := h73046;
    let u11 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h67929 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step102931 (p2210 p2440 p2542 p2922 p2925 p3399 p3555 p3741 p4811 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73318 : p2925 ∨ p2922)
    (h73270 : p2542 ∨ p2440)
    (h67566 : (¬ p2925) ∨ (¬ p2542) ∨ (¬ p3399) ∨ (¬ p4811) ∨ (¬ p3741) ∨ (¬ p3555))
    : (¬ p3399) ∨ p2210 ∨ p2922 ∨ (¬ p3741) ∨ (¬ p4811) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2925 := (Or.elim h73318 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h67566 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step102932 (p2088 p2156 p2563 p3146 p3646 p3692 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73436 : p3646 ∨ p2156)
    (h67632 : (¬ p3692) ∨ (¬ p2563) ∨ (¬ p3646) ∨ (¬ p2088))
    : p3146 ∨ p2156 ∨ (¬ p2563) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h67632 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step102934 (p2088 p2156 p3146 p3646 p3692 p4509 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73436 : p3646 ∨ p2156)
    (h67673 : (¬ p3692) ∨ (¬ p4509) ∨ (¬ p3646) ∨ (¬ p2088))
    : p3146 ∨ p2156 ∨ (¬ p4509) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h67673 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step102936 (p2088 p2274 p2383 p3146 p3692 p3857 p4356 p4612 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73668 : p4612 ∨ p2383)
    (h73479 : (¬ p2088) ∨ (¬ p3857))
    (h72336 : (¬ p4356) ∨ (¬ p3692) ∨ (¬ p4612) ∨ (¬ p2274) ∨ p3857)
    : (¬ p2274) ∨ p3146 ∨ p2383 ∨ (¬ p4356) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4612 := (Or.elim h73668 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : (¬ p3857) := (Or.elim h73479 (fun q0 => (False.elim (q0 u4))) (fun r0 => r0));
    (Or.elim h72336 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (u7 r3)))))))))))

theorem step102939 (p2230 p2274 p2307 p2589 p3097 p3389 p4717 p4718 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73284 : p2589 ∨ p2230)
    (h67622 : (¬ p2589) ∨ (¬ p4718) ∨ (¬ p4717) ∨ (¬ p3097) ∨ (¬ p3389) ∨ (¬ p2307))
    : (¬ p2307) ∨ p2274 ∨ (¬ p4717) ∨ p2230 ∨ (¬ p3389) ∨ (¬ p4718) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h67622 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step102940 (p2295 p2352 p2383 p2387 p2668 p3324 p3389 p4711 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h73386 : p3324 ∨ p2668)
    (h67543 : (¬ p2352) ∨ (¬ p2387) ∨ (¬ p3324) ∨ (¬ p2295) ∨ (¬ p3389) ∨ (¬ p4711))
    : (¬ p3389) ∨ (¬ p4711) ∨ (¬ p2352) ∨ (¬ p2295) ∨ p2383 ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4711 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u7 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h67543 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step102941 (p2608 p2922 p2925 p3389 p3399 p3954 p4366 : Prop)
    (h73318 : p2925 ∨ p2922)
    (h73498 : p3954 ∨ p2608)
    (h73569 : (¬ p3399) ∨ (¬ p4366))
    (h72337 : (¬ p2925) ∨ (¬ p3389) ∨ p4366 ∨ (¬ p3954))
    : p2922 ∨ p2608 ∨ (¬ p3399) ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2925 := (Or.elim h73318 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : (¬ p4366) := (Or.elim h73569 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h72337 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step102942 (p2481 p2881 p3201 p3641 p3874 p4277 p4383 p5203 : Prop)
    (h73484 : p3874 ∨ p3641)
    (h68045 : (¬ p3874) ∨ (¬ p3201) ∨ (¬ p2481) ∨ (¬ p5203) ∨ (¬ p4383) ∨ (¬ p4277) ∨ (¬ p2881))
    : (¬ p2481) ∨ (¬ p4383) ∨ p3641 ∨ (¬ p3201) ∨ (¬ p4277) ∨ (¬ p2881) ∨ (¬ p5203) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2481 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h68045 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step102947 (p2307 p2331 p2651 p2657 p2727 p4582 : Prop)
    (h73650 : p4582 ∨ (¬ p2331))
    (h73288 : p2657 ∨ p2651)
    (h67659 : (¬ p4582) ∨ (¬ p2307) ∨ (¬ p2657) ∨ (¬ p2727))
    : (¬ p2331) ∨ (¬ p2307) ∨ p2651 ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4582 := (Or.elim h73650 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h67659 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step102948 (p2363 p3189 p3256 p3449 p4347 p5077 : Prop)
    (h73910 : p5077 ∨ (¬ p3189))
    (h73560 : p4347 ∨ p2363)
    (h67819 : (¬ p4347) ∨ (¬ p3449) ∨ (¬ p5077) ∨ (¬ p3256))
    : (¬ p3189) ∨ (¬ p3256) ∨ p2363 ∨ (¬ p3449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5077 := (Or.elim h73910 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h67819 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step102951 (p2156 p2284 p3125 p3654 p3744 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h67467 : p2284 ∨ (¬ p3654) ∨ (¬ p3744) ∨ (¬ p2156))
    : (¬ p3654) ∨ p2284 ∨ (¬ p2156) ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h67467 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step102952 (p2156 p2440 p2563 p3646 p4714 : Prop)
    (h73435 : (¬ p2156) ∨ (¬ p3646))
    (h73720 : p4714 ∨ p2563)
    (h68210 : (¬ p2440) ∨ p3646 ∨ (¬ p4714))
    : (¬ p2440) ∨ (¬ p2156) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3646) := (Or.elim h73435 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u4 : p4714 := (Or.elim h73720 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h68210 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step102954 (p2608 p2651 p2657 p2727 p3361 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h67780 : (¬ p2657) ∨ (¬ p2608) ∨ (¬ p3361) ∨ (¬ p2727))
    : (¬ p2727) ∨ (¬ p2608) ∨ p2651 ∨ (¬ p3361) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h67780 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step102955 (p2331 p2363 p2963 p3256 p3286 p4347 p4774 p5110 : Prop)
    (h73924 : p5110 ∨ (¬ p3256))
    (h73338 : p2963 ∨ p2331)
    (h73560 : p4347 ∨ p2363)
    (h67441 : (¬ p5110) ∨ (¬ p2963) ∨ (¬ p3286) ∨ (¬ p4774) ∨ (¬ p4347))
    : (¬ p3286) ∨ (¬ p3256) ∨ p2331 ∨ p2363 ∨ (¬ p4774) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3286 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5110 := (Or.elim h73924 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u6 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h67441 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step102960 (p2274 p2284 p2427 p2651 p2657 p2807 p3872 p4235 p4705 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73288 : p2657 ∨ p2651)
    (h67593 : (¬ p2284) ∨ (¬ p2807) ∨ (¬ p4705) ∨ (¬ p4235) ∨ (¬ p2274) ∨ (¬ p3872) ∨ (¬ p2657))
    : (¬ p2284) ∨ (¬ p3872) ∨ (¬ p4705) ∨ (¬ p2274) ∨ (¬ p2807) ∨ p2427 ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u8 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h67593 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u8)))))))))))))))

theorem step102961 (p2249 p2307 p2313 p2331 p2352 p2641 p2807 p3956 p4579 p4976 : Prop)
    (h73648 : p4579 ∨ p2331)
    (h73500 : p3956 ∨ p2352)
    (h73237 : (¬ p2307) ∨ (¬ p2313))
    (h72343 : (¬ p3956) ∨ (¬ p2641) ∨ (¬ p2807) ∨ (¬ p2249) ∨ (¬ p4579) ∨ (¬ p4976) ∨ p2313)
    : p2331 ∨ (¬ p2641) ∨ p2352 ∨ (¬ p2807) ∨ (¬ p2249) ∨ (¬ p4976) ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4976 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4579 := (Or.elim h73648 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : (¬ p2313) := (Or.elim h73237 (fun q0 => (False.elim (q0 u6))) (fun r0 => r0));
    (Or.elim h72343 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (u9 r5)))))))))))))))

theorem step102964 (p2230 p2563 p2630 p2662 p2810 p2881 p3051 p3556 p3570 p4110 p4535 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73516 : p4110 ∨ p2563)
    (h73414 : p3556 ∨ p3051)
    (h73622 : p4535 ∨ p2230)
    (h73418 : p3570 ∨ p2881)
    (h67782 : (¬ p4535) ∨ (¬ p3556) ∨ (¬ p4110) ∨ (¬ p3570) ∨ (¬ p2810) ∨ (¬ p2662))
    : p2630 ∨ (¬ p2662) ∨ p2563 ∨ p3051 ∨ p2230 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p4535 := (Or.elim h73622 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h67782 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step102967 (p2230 p2440 p2598 p2641 p2663 p3362 p3367 p3585 p4117 p4154 p4257 p4281 p4972 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h73526 : p4154 ∨ p2641)
    (h72344 : (¬ p2440) ∨ (¬ p2230) ∨ (¬ p4117) ∨ (¬ p4154) ∨ (¬ p4972) ∨ (¬ p3585) ∨ (¬ p4257) ∨ (¬ p3362) ∨ (¬ p2598) ∨ (¬ p2663) ∨ (¬ p4281))
    : (¬ p2230) ∨ p3367 ∨ (¬ p4117) ∨ (¬ p2598) ∨ (¬ p4972) ∨ p2641 ∨ (¬ p2440) ∨ (¬ p4257) ∨ (¬ p3362) ∨ (¬ p2663) ∨ (¬ p4281) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3367) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h72344 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (False.elim (r9 u10)))))))))))))))))))))))

theorem step102969 (p2363 p2641 p2727 p3063 p4111 p4758 p4975 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73746 : p4758 ∨ (¬ p2641))
    (h67936 : (¬ p4758) ∨ (¬ p3063) ∨ (¬ p4975) ∨ (¬ p2363) ∨ (¬ p4111))
    : (¬ p3063) ∨ p2727 ∨ (¬ p4975) ∨ (¬ p2363) ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4758 := (Or.elim h73746 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    (Or.elim h67936 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step102974 (p2187 p2440 p2542 p2668 p3016 p3324 p4715 p4971 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h73858 : p4971 ∨ p3016)
    (h73270 : p2542 ∨ p2440)
    (h67835 : (¬ p4971) ∨ (¬ p3324) ∨ (¬ p2542) ∨ (¬ p2187) ∨ (¬ p4715))
    : p2668 ∨ p3016 ∨ (¬ p2187) ∨ p2440 ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2668) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4971 := (Or.elim h73858 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h67835 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step102976 (p2177 p2274 p2299 p2668 p2881 p3324 p4138 p4557 p4564 : Prop)
    (h73636 : p4557 ∨ (¬ p2274))
    (h73234 : p2299 ∨ p2177)
    (h73386 : p3324 ∨ p2668)
    (h67804 : (¬ p2881) ∨ (¬ p4564) ∨ (¬ p3324) ∨ (¬ p2299) ∨ (¬ p4138) ∨ (¬ p4557))
    : (¬ p2881) ∨ (¬ p2274) ∨ p2177 ∨ (¬ p4564) ∨ (¬ p4138) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h67804 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step102977 (p2352 p2440 p2542 p2668 p3083 p3324 p4597 p4715 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73658 : p4597 ∨ (¬ p2352))
    (h73386 : p3324 ∨ p2668)
    (h67740 : (¬ p4597) ∨ p3083 ∨ (¬ p3324) ∨ (¬ p2542) ∨ (¬ p4715))
    : p3083 ∨ p2440 ∨ (¬ p2352) ∨ (¬ p4715) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4597 := (Or.elim h73658 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u7 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h67740 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step102979 (p2459 p2528 p2573 p2579 p3355 p4348 p4438 p4694 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73710 : p4694 ∨ (¬ p2528))
    (h73562 : p4348 ∨ p2459)
    (h67762 : (¬ p4694) ∨ (¬ p3355) ∨ (¬ p2579) ∨ (¬ p4438) ∨ (¬ p4348))
    : (¬ p3355) ∨ (¬ p4438) ∨ p2573 ∨ (¬ p2528) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3355 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4694 := (Or.elim h73710 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u7 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h67762 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step102985 (p2088 p2156 p2177 p2459 p3646 p3743 p4500 p4559 p4665 : Prop)
    (h73602 : p4500 ∨ p2177)
    (h73436 : p3646 ∨ p2156)
    (h73696 : p4665 ∨ p2459)
    (h67674 : (¬ p4665) ∨ (¬ p4500) ∨ (¬ p4559) ∨ (¬ p3646) ∨ (¬ p3743) ∨ (¬ p2088))
    : p2177 ∨ (¬ p4559) ∨ p2156 ∨ p2459 ∨ (¬ p2088) ∨ (¬ p3743) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2177) := (fun h => hn (Or.inl h));
    let u1 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4500 := (Or.elim h73602 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p4665 := (Or.elim h73696 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h67674 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step102990 (p2264 p2727 p2881 p2911 p3016 p3574 p3644 p3872 p4111 p4711 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73518 : p4111 ∨ p2727)
    (h73422 : p3574 ∨ p3016)
    (h68057 : (¬ p3644) ∨ (¬ p2264) ∨ (¬ p3574) ∨ (¬ p4711) ∨ (¬ p4111) ∨ (¬ p2881) ∨ (¬ p3872))
    : p2911 ∨ (¬ p2264) ∨ p2727 ∨ p3016 ∨ (¬ p4711) ∨ (¬ p2881) ∨ (¬ p3872) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4711 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h68057 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step102999 (p2210 p2241 p2509 p2563 p3379 p3452 p4110 p4608 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73516 : p4110 ∨ p2563)
    (h68043 : (¬ p3452) ∨ (¬ p2210) ∨ (¬ p2509) ∨ (¬ p2241) ∨ (¬ p4608) ∨ (¬ p4110))
    : (¬ p2241) ∨ p3379 ∨ (¬ p2509) ∨ p2563 ∨ (¬ p4608) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h68043 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step103009 (p2241 p2608 p3367 p3585 p3954 p4749 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73428 : p3585 ∨ p3367)
    (h67972 : (¬ p2241) ∨ (¬ p4749) ∨ (¬ p3954) ∨ (¬ p3585))
    : p2608 ∨ (¬ p2241) ∨ (¬ p4749) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h67972 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step103015 (p2098 p2668 p2774 p3324 p4846 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h67849 : p2774 ∨ (¬ p3324) ∨ (¬ p4846) ∨ (¬ p2098))
    : (¬ p2098) ∨ p2668 ∨ (¬ p4846) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2668) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4846 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h67849 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step103018 (p2230 p2440 p2542 p2630 p2797 p2810 p4195 p4715 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73270 : p2542 ∨ p2440)
    (h73315 : (¬ p2630) ∨ (¬ p2810))
    (h67833 : (¬ p4195) ∨ (¬ p2230) ∨ (¬ p2542) ∨ (¬ p4715) ∨ (¬ p2630) ∨ p2810)
    : p2797 ∨ (¬ p2230) ∨ (¬ p4715) ∨ p2440 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : (¬ p2810) := (Or.elim h73315 (fun q0 => (False.elim (q0 u4))) (fun r0 => r0));
    (Or.elim h67833 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (u7 r4)))))))))))))

theorem step103019 (p2493 p2630 p2797 p2992 p3136 p4195 p4315 p4814 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73532 : p4195 ∨ p2797)
    (h67544 : (¬ p2630) ∨ (¬ p2493) ∨ (¬ p4195) ∨ (¬ p4315) ∨ (¬ p2992) ∨ (¬ p4814))
    : p3136 ∨ (¬ p2992) ∨ (¬ p2493) ∨ p2797 ∨ (¬ p4814) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h67544 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step103020 (p2630 p2737 p2743 p2797 p2810 p3367 p4195 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73532 : p4195 ∨ p2797)
    (h73315 : (¬ p2630) ∨ (¬ p2810))
    (h67830 : (¬ p4195) ∨ (¬ p3367) ∨ p2810 ∨ (¬ p2743))
    : p2737 ∨ p2797 ∨ (¬ p3367) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : (¬ p2810) := (Or.elim h73315 (fun q0 => (False.elim (q0 u3))) (fun r0 => r0));
    (Or.elim h67830 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step103023 (p2598 p2630 p2727 p4111 p4751 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73742 : p4751 ∨ (¬ p2630))
    (h72364 : (¬ p4111) ∨ (¬ p2598) ∨ (¬ p4751))
    : p2727 ∨ (¬ p2630) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p4751 := (Or.elim h73742 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h72364 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u4)))))))

theorem step103025 (p2737 p2743 p2850 p3136 p3367 p3684 p4315 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73442 : p3684 ∨ p2850)
    (h73550 : p4315 ∨ p3136)
    (h67476 : (¬ p3367) ∨ (¬ p3684) ∨ (¬ p4315) ∨ (¬ p2743))
    : p2737 ∨ (¬ p3367) ∨ p2850 ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h67476 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step103030 (p2363 p2459 p2881 p4347 p4559 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h68020 : (¬ p2459) ∨ (¬ p2881) ∨ (¬ p4347) ∨ (¬ p4559))
    : p2363 ∨ (¬ p2881) ∨ (¬ p4559) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h68020 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step103032 (p2177 p2274 p2352 p2881 p3956 p3958 p4500 p4557 : Prop)
    (h73636 : p4557 ∨ (¬ p2274))
    (h73500 : p3956 ∨ p2352)
    (h73602 : p4500 ∨ p2177)
    (h67995 : (¬ p4500) ∨ (¬ p3956) ∨ (¬ p2881) ∨ (¬ p3958) ∨ (¬ p4557))
    : (¬ p2881) ∨ (¬ p2274) ∨ p2352 ∨ (¬ p3958) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4500 := (Or.elim h73602 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h67995 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step103037 (p2440 p2563 p2598 p2727 p3366 p3367 p3585 p4110 p4111 p4728 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73516 : p4110 ∨ p2563)
    (h73428 : p3585 ∨ p3367)
    (h73730 : p4728 ∨ (¬ p2598))
    (h72368 : (¬ p3585) ∨ (¬ p4728) ∨ (¬ p4110) ∨ (¬ p3366) ∨ (¬ p4111) ∨ (¬ p2440))
    : p2727 ∨ (¬ p3366) ∨ p2563 ∨ (¬ p2440) ∨ p3367 ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p4728 := (Or.elim h73730 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    (Or.elim h72368 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step103039 (p2440 p2563 p2608 p2839 p3367 p3585 p3954 p4110 p4753 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73516 : p4110 ∨ p2563)
    (h73428 : p3585 ∨ p3367)
    (h67826 : (¬ p3585) ∨ (¬ p2440) ∨ (¬ p2839) ∨ (¬ p3954) ∨ (¬ p4110) ∨ (¬ p4753))
    : (¬ p2839) ∨ p2608 ∨ p2563 ∨ (¬ p2440) ∨ (¬ p4753) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2839 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h67826 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step103040 (p2230 p2589 p2659 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h67571 : p2659 ∨ (¬ p2589))
    : p2659 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2659) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2230) := (fun h => hn (Or.inr h));
    let u2 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h67571 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step103041 (p2230 p2363 p2528 p2589 p3146 p3355 p3692 p4347 p4434 p4694 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73448 : p3692 ∨ p3146)
    (h73284 : p2589 ∨ p2230)
    (h73710 : p4694 ∨ (¬ p2528))
    (h67609 : (¬ p4694) ∨ (¬ p3355) ∨ (¬ p2589) ∨ (¬ p4347) ∨ (¬ p4434) ∨ (¬ p3692))
    : p2363 ∨ (¬ p3355) ∨ p3146 ∨ p2230 ∨ (¬ p4434) ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p4694 := (Or.elim h73710 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    (Or.elim h67609 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step103042 (p2177 p2187 p2230 p2563 p2589 p3363 p3367 p3585 p3989 p4110 p4140 p4500 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h73516 : p4110 ∨ p2563)
    (h73284 : p2589 ∨ p2230)
    (h73502 : p3989 ∨ p2187)
    (h73602 : p4500 ∨ p2177)
    (h67797 : (¬ p3989) ∨ (¬ p2589) ∨ (¬ p3585) ∨ (¬ p4110) ∨ (¬ p3363) ∨ (¬ p4500) ∨ (¬ p4140))
    : p3367 ∨ (¬ p3363) ∨ (¬ p4140) ∨ p2563 ∨ p2230 ∨ p2187 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3367) := (fun h => hn (Or.inl h));
    let u1 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p4500 := (Or.elim h73602 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h67797 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step103043 (p2210 p2230 p2589 p3379 p5189 : Prop)
    (h73948 : p5189 ∨ p3379)
    (h73284 : p2589 ∨ p2230)
    (h68186 : (¬ p5189) ∨ (¬ p2210) ∨ (¬ p2589))
    : p3379 ∨ (¬ p2210) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p5189 := (Or.elim h73948 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h68186 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step103044 (p2630 p2696 p2727 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h72370 : (¬ p4111) ∨ (¬ p2630) ∨ (¬ p2696))
    : p2727 ∨ (¬ p2630) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h72370 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step103045 (p2630 p2696 p2737 p2774 p2780 p4972 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h68080 : (¬ p2696) ∨ (¬ p2630) ∨ (¬ p2780) ∨ (¬ p4972) ∨ (¬ p2737))
    : p2774 ∨ (¬ p2737) ∨ (¬ p4972) ∨ (¬ p2696) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h68080 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step103047 (p2187 p2274 p2318 p2319 p3246 p3743 p3872 p3989 p4138 p4668 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h72372 : (¬ p3246) ∨ (¬ p3989) ∨ (¬ p4138) ∨ (¬ p4668) ∨ (¬ p2318) ∨ (¬ p2319) ∨ (¬ p3872) ∨ (¬ p2274) ∨ (¬ p3743))
    : (¬ p2319) ∨ (¬ p3246) ∨ (¬ p2274) ∨ (¬ p3872) ∨ (¬ p4138) ∨ p2187 ∨ (¬ p4668) ∨ (¬ p2318) ∨ (¬ p3743) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2318 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h72372 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step103049 (p2177 p2299 p2761 p3246 p3266 p3461 p4191 p4444 p4559 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73234 : p2299 ∨ p2177)
    (h73580 : p4444 ∨ p3266)
    (h67895 : (¬ p2761) ∨ (¬ p4191) ∨ (¬ p4444) ∨ (¬ p3246) ∨ (¬ p2299) ∨ (¬ p4559))
    : p3461 ∨ (¬ p2761) ∨ p2177 ∨ p3266 ∨ (¬ p3246) ∨ (¬ p4559) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h67895 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step103053 (p2396 p2417 p2427 p2563 p4107 p4110 p4558 p4645 : Prop)
    (h73686 : p4645 ∨ (¬ p2427))
    (h73516 : p4110 ∨ p2563)
    (h73514 : p4107 ∨ p2396)
    (h67382 : (¬ p4110) ∨ (¬ p4558) ∨ (¬ p4107) ∨ (¬ p4645) ∨ (¬ p2417))
    : (¬ p2417) ∨ (¬ p2427) ∨ (¬ p4558) ∨ p2563 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4645 := (Or.elim h73686 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h67382 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step103054 (p2417 p3192 p3246 p3276 p3461 p3690 p4140 p4191 p4712 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73446 : p3690 ∨ p3246)
    (h67677 : (¬ p3690) ∨ (¬ p3276) ∨ (¬ p2417) ∨ (¬ p3192) ∨ (¬ p4191) ∨ (¬ p4712) ∨ (¬ p4140))
    : (¬ p3276) ∨ p3461 ∨ (¬ p3192) ∨ (¬ p4140) ∨ (¬ p2417) ∨ p3246 ∨ (¬ p4712) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h67677 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step103056 (p2177 p2264 p2363 p3256 p4347 p4361 p4500 p4551 : Prop)
    (h73632 : p4551 ∨ (¬ p2264))
    (h73602 : p4500 ∨ p2177)
    (h73560 : p4347 ∨ p2363)
    (h67489 : (¬ p4551) ∨ (¬ p3256) ∨ (¬ p4347) ∨ (¬ p4361) ∨ (¬ p4500))
    : (¬ p3256) ∨ (¬ p2264) ∨ p2177 ∨ (¬ p4361) ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4551 := (Or.elim h73632 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u6 : p4500 := (Or.elim h73602 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h67489 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step103057 (p2177 p2295 p2331 p2696 p2774 p2780 p4788 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73760 : p4788 ∨ (¬ p2696))
    (h67429 : (¬ p4788) ∨ (¬ p2780) ∨ (¬ p2177) ∨ (¬ p2295) ∨ (¬ p2331))
    : p2774 ∨ (¬ p2295) ∨ (¬ p2696) ∨ (¬ p2177) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4788 := (Or.elim h73760 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h67429 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step103059 (p2563 p2829 p2839 p2860 p3688 p3758 p4428 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73456 : p3758 ∨ p2860)
    (h67777 : (¬ p2563) ∨ (¬ p2839) ∨ (¬ p3688) ∨ (¬ p4428) ∨ (¬ p3758))
    : p2829 ∨ (¬ p2839) ∨ (¬ p2563) ∨ p2860 ∨ (¬ p4428) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4428 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h67777 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step103066 (p2307 p2553 p3389 p4707 : Prop)
    (h73716 : p4707 ∨ p2553)
    (h67536 : (¬ p4707) ∨ p3389 ∨ (¬ p2307))
    : (¬ p2307) ∨ p3389 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4707 := (Or.elim h73716 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h67536 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step103068 (p2132 p2177 p2299 p2860 p2881 p3570 : Prop)
    (h73417 : (¬ p2881) ∨ (¬ p3570))
    (h73234 : p2299 ∨ p2177)
    (h67626 : p3570 ∨ (¬ p2299) ∨ (¬ p2860) ∨ (¬ p2132))
    : (¬ p2860) ∨ (¬ p2132) ∨ (¬ p2881) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2860 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3570) := (Or.elim h73417 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h67626 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step103069 (p2630 p2668 p2819 p3005 p4358 p4772 p4972 : Prop)
    (h73752 : p4772 ∨ (¬ p2668))
    (h73564 : p4358 ∨ p2819)
    (h68190 : (¬ p4772) ∨ p3005 ∨ (¬ p4358) ∨ (¬ p4972) ∨ (¬ p2630))
    : p3005 ∨ (¬ p2668) ∨ p2819 ∨ (¬ p2630) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4772 := (Or.elim h73752 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h68190 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step103070 (p2383 p2387 p2651 p2668 p3166 p4772 p4972 : Prop)
    (h73752 : p4772 ∨ (¬ p2668))
    (h73246 : p2387 ∨ p2383)
    (h67501 : (¬ p4772) ∨ (¬ p4972) ∨ (¬ p2651) ∨ p3166 ∨ (¬ p2387))
    : (¬ p2668) ∨ p3166 ∨ p2383 ∨ (¬ p2651) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4772 := (Or.elim h73752 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u6 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h67501 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step103071 (p2630 p2651 p2727 p2810 p2829 p3589 p3688 p4117 p4842 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73316 : p2810 ∨ p2630)
    (h72375 : (¬ p3688) ∨ (¬ p3589) ∨ (¬ p2810) ∨ (¬ p4842) ∨ (¬ p4117) ∨ (¬ p2651) ∨ (¬ p2727))
    : p2829 ∨ (¬ p3589) ∨ (¬ p4117) ∨ p2630 ∨ (¬ p4842) ∨ (¬ p2651) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h72375 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step103074 (p2427 p2563 p2891 p3379 p3452 p3486 p4110 p4119 p4202 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h73516 : p4110 ∨ p2563)
    (h73394 : p3452 ∨ p3379)
    (h67685 : (¬ p3486) ∨ (¬ p3452) ∨ (¬ p4202) ∨ (¬ p4119) ∨ (¬ p2427) ∨ (¬ p4110))
    : p2891 ∨ (¬ p2427) ∨ (¬ p4202) ∨ p2563 ∨ (¬ p4119) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2891) := (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h67685 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step103075 (p2190 p2427 p2528 p2534 p3146 p4558 p5057 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73898 : p5057 ∨ (¬ p3146))
    (h68249 : (¬ p5057) ∨ (¬ p2534) ∨ (¬ p2427) ∨ (¬ p2190) ∨ (¬ p4558))
    : (¬ p2190) ∨ p2528 ∨ (¬ p4558) ∨ (¬ p2427) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2190 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p5057 := (Or.elim h73898 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    (Or.elim h68249 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step103078 (p2166 p2210 p2608 p3073 p3954 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h67554 : (¬ p2210) ∨ (¬ p3073) ∨ (¬ p3954) ∨ (¬ p2166))
    : (¬ p3073) ∨ p2608 ∨ (¬ p2166) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h67554 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step103079 (p2088 p2166 p2528 p2534 p3146 p4539 p4607 p4632 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h68245 : (¬ p2534) ∨ (¬ p2166) ∨ (¬ p3146) ∨ (¬ p4607) ∨ (¬ p4539) ∨ (¬ p4632) ∨ (¬ p2088))
    : p2528 ∨ (¬ p3146) ∨ (¬ p4632) ∨ (¬ p4539) ∨ (¬ p2088) ∨ (¬ p4607) ∨ (¬ p2166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4539 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4607 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h68245 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step103080 (p2156 p2210 p2563 p2608 p3954 p4110 p4523 p4877 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73616 : p4523 ∨ (¬ p2210))
    (h73516 : p4110 ∨ p2563)
    (h68207 : (¬ p4523) ∨ (¬ p2156) ∨ (¬ p4110) ∨ (¬ p4877) ∨ (¬ p3954))
    : p2608 ∨ (¬ p2210) ∨ (¬ p4877) ∨ (¬ p2156) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4523 := (Or.elim h73616 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h68207 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step103081 (p2192 p2210 p2274 p2363 p3063 p4515 : Prop)
    (h73612 : p4515 ∨ (¬ p2192))
    (h67404 : (¬ p4515) ∨ (¬ p2210) ∨ (¬ p2363) ∨ (¬ p3063) ∨ (¬ p2274))
    : (¬ p3063) ∨ (¬ p2274) ∨ (¬ p2363) ∨ (¬ p2210) ∨ (¬ p2192) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4515 := (Or.elim h73612 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    (Or.elim h67404 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step103082 (p2437 p2608 p2662 p2727 p2911 p3201 p3389 p3540 p3742 p3876 p4111 : Prop)
    (h73485 : (¬ p3201) ∨ (¬ p3876))
    (h73402 : p3540 ∨ p3389)
    (h73518 : p4111 ∨ p2727)
    (h73452 : p3742 ∨ p2437)
    (h67427 : p3876 ∨ (¬ p2608) ∨ (¬ p2911) ∨ (¬ p3540) ∨ (¬ p3742) ∨ (¬ p4111) ∨ (¬ p2662))
    : (¬ p3201) ∨ p3389 ∨ p2727 ∨ (¬ p2662) ∨ p2437 ∨ (¬ p2608) ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3201 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p3876) := (Or.elim h73485 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u8 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h67427 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step103084 (p2190 p2284 p2528 p2534 p3146 p4705 p5057 : Prop)
    (h73898 : p5057 ∨ (¬ p3146))
    (h73268 : p2534 ∨ p2528)
    (h68232 : (¬ p5057) ∨ (¬ p2534) ∨ (¬ p2284) ∨ (¬ p2190) ∨ (¬ p4705))
    : (¬ p2190) ∨ (¬ p3146) ∨ (¬ p4705) ∨ (¬ p2284) ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2190 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5057 := (Or.elim h73898 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u6 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h68232 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step103085 (p2177 p2264 p2274 p2299 p3097 p3553 p4560 : Prop)
    (h73409 : (¬ p2264) ∨ (¬ p3553))
    (h73352 : p3097 ∨ p2274)
    (h73234 : p2299 ∨ p2177)
    (h72955 : p4560)
    (h67600 : p3553 ∨ (¬ p4560) ∨ (¬ p3097) ∨ (¬ p2299))
    : (¬ p2264) ∨ p2274 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3553) := (Or.elim h73409 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4560 := h72955;
    (Or.elim h67600 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step103086 (p3201 p3389 p3425 p5081 : Prop)
    (h73912 : p5081 ∨ p3201)
    (h67371 : (¬ p3389) ∨ (¬ p3425) ∨ (¬ p5081))
    : p3201 ∨ (¬ p3389) ∨ (¬ p3425) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p5081 := (Or.elim h73912 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h67371 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step103087 (p2241 p2244 p2331 p2727 p2963 p3379 p4812 p4972 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73224 : p2244 ∨ p2241)
    (h73772 : p4812 ∨ (¬ p2727))
    (h67682 : (¬ p2244) ∨ (¬ p3379) ∨ (¬ p4972) ∨ (¬ p2963) ∨ (¬ p4812))
    : p2331 ∨ p2241 ∨ (¬ p4972) ∨ (¬ p3379) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2244 := (Or.elim h73224 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4812 := (Or.elim h73772 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    (Or.elim h67682 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step103089 (p2156 p2284 p2563 p2651 p2657 p2727 p3646 p4110 p4565 : Prop)
    (h73640 : p4565 ∨ (¬ p2284))
    (h73436 : p3646 ∨ p2156)
    (h73288 : p2657 ∨ p2651)
    (h73516 : p4110 ∨ p2563)
    (h67665 : (¬ p4565) ∨ (¬ p4110) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p3646))
    : (¬ p2284) ∨ (¬ p2727) ∨ p2156 ∨ p2651 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4565 := (Or.elim h73640 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h67665 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step103091 (p2156 p2220 p2352 p3646 p3956 p3958 p4120 : Prop)
    (h73521 : (¬ p2220) ∨ (¬ p4120))
    (h73436 : p3646 ∨ p2156)
    (h73500 : p3956 ∨ p2352)
    (h68110 : p4120 ∨ (¬ p3956) ∨ (¬ p3646) ∨ (¬ p3958))
    : (¬ p2220) ∨ p2156 ∨ p2352 ∨ (¬ p3958) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4120) := (Or.elim h73521 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h68110 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step103093 (p2177 p2307 p2459 p3093 p3527 p3548 p5022 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h67394 : (¬ p2177) ∨ (¬ p3548) ∨ (¬ p2307) ∨ (¬ p3093) ∨ (¬ p5022) ∨ (¬ p2459))
    : (¬ p2307) ∨ (¬ p5022) ∨ (¬ p2177) ∨ (¬ p3093) ∨ (¬ p2459) ∨ p3527 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5022 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h67394 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step103100 (p2088 p2274 p2363 p2608 p2737 p2747 p4557 p4602 p4732 : Prop)
    (h73732 : p4732 ∨ p2608)
    (h73302 : p2747 ∨ (¬ p2737))
    (h73636 : p4557 ∨ (¬ p2274))
    (h73662 : p4602 ∨ (¬ p2363))
    (h68870 : (¬ p4557) ∨ (¬ p2747) ∨ (¬ p2088) ∨ (¬ p4732) ∨ (¬ p4602))
    : p2608 ∨ (¬ p2088) ∨ (¬ p2737) ∨ (¬ p2274) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4732 := (Or.elim h73732 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2747 := (Or.elim h73302 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u7 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u8 : p4602 := (Or.elim h73662 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    (Or.elim h68870 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u8)))))))))))

theorem step103101 (p2088 p2363 p2563 p2608 p2737 p2747 p4602 p4714 p4732 : Prop)
    (h73732 : p4732 ∨ p2608)
    (h73720 : p4714 ∨ p2563)
    (h73662 : p4602 ∨ (¬ p2363))
    (h73302 : p2747 ∨ (¬ p2737))
    (h69075 : (¬ p4714) ∨ (¬ p2747) ∨ (¬ p2088) ∨ (¬ p4732) ∨ (¬ p4602))
    : p2608 ∨ (¬ p2088) ∨ p2563 ∨ (¬ p2363) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4732 := (Or.elim h73732 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4714 := (Or.elim h73720 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4602 := (Or.elim h73662 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u8 : p2747 := (Or.elim h73302 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    (Or.elim h69075 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step103102 (p2274 p2563 p2696 p2737 p2850 p3365 p3367 p4734 p4883 : Prop)
    (h73808 : p4883 ∨ (¬ p2850))
    (h73390 : p3365 ∨ p2696)
    (h72735 : p4734)
    (h68819 : (¬ p4883) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p2563) ∨ (¬ p2274) ∨ (¬ p2737) ∨ (¬ p4734))
    : (¬ p2737) ∨ (¬ p2850) ∨ (¬ p2274) ∨ p2696 ∨ (¬ p3367) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4883 := (Or.elim h73808 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u7 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p4734 := h72735;
    (Or.elim h68819 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (r5 u8)))))))))))))))

theorem step103103 (p2088 p2363 p2608 p2696 p2737 p2747 p3323 p3367 p3379 p4602 p4732 p4788 p5189 : Prop)
    (h73662 : p4602 ∨ (¬ p2363))
    (h73948 : p5189 ∨ p3379)
    (h73732 : p4732 ∨ p2608)
    (h73760 : p4788 ∨ (¬ p2696))
    (h73302 : p2747 ∨ (¬ p2737))
    (h69459 : (¬ p3323) ∨ (¬ p3367) ∨ (¬ p5189) ∨ (¬ p4788) ∨ (¬ p2747) ∨ (¬ p2088) ∨ (¬ p4732) ∨ (¬ p4602))
    : (¬ p3323) ∨ (¬ p3367) ∨ (¬ p2363) ∨ p3379 ∨ p2608 ∨ (¬ p2088) ∨ (¬ p2696) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4602 := (Or.elim h73662 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u9 : p5189 := (Or.elim h73948 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4732 := (Or.elim h73732 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p4788 := (Or.elim h73760 (fun q0 => q0) (fun r0 => (False.elim (r0 u6))));
    let u12 : p2747 := (Or.elim h73302 (fun q0 => q0) (fun r0 => (False.elim (r0 u7))));
    (Or.elim h69459 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u8)))))))))))))))))

theorem step103108 (p2088 p2363 p2459 p2608 p2696 p2737 p2747 p3367 p4602 p4667 p4732 p4788 p5215 : Prop)
    (h73732 : p4732 ∨ p2608)
    (h73662 : p4602 ∨ (¬ p2363))
    (h73962 : p5215 ∨ (¬ p3367))
    (h73760 : p4788 ∨ (¬ p2696))
    (h73698 : p4667 ∨ (¬ p2459))
    (h73302 : p2747 ∨ (¬ p2737))
    (h69424 : (¬ p5215) ∨ (¬ p4667) ∨ (¬ p4788) ∨ (¬ p2747) ∨ (¬ p2088) ∨ (¬ p4732) ∨ (¬ p4602))
    : p2608 ∨ (¬ p2363) ∨ (¬ p3367) ∨ (¬ p2088) ∨ (¬ p2696) ∨ (¬ p2459) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4732 := (Or.elim h73732 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p4602 := (Or.elim h73662 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u9 : p5215 := (Or.elim h73962 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u10 : p4788 := (Or.elim h73760 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u11 : p4667 := (Or.elim h73698 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    let u12 : p2747 := (Or.elim h73302 (fun q0 => q0) (fun r0 => (False.elim (r0 u6))));
    (Or.elim h69424 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (False.elim (r5 u8)))))))))))))))

theorem step103109 (p2274 p2493 p2553 p2577 p2578 p2630 p2696 p3016 p3097 p4814 p4971 p5191 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73858 : p4971 ∨ p3016)
    (h69286 : (¬ p2493) ∨ (¬ p2578) ∨ (¬ p2577) ∨ (¬ p2553) ∨ (¬ p5191) ∨ (¬ p4971) ∨ (¬ p4814) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p3097))
    : (¬ p2553) ∨ p2274 ∨ (¬ p2493) ∨ (¬ p2696) ∨ (¬ p2630) ∨ (¬ p2578) ∨ p3016 ∨ (¬ p2577) ∨ (¬ p5191) ∨ (¬ p4814) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p4971 := (Or.elim h73858 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h69286 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u10)))))))))))))))))))))

theorem step103110 (p2839 p2972 p2982 p3367 p3585 p4876 p4884 p4948 : Prop)
    (h73804 : p4876 ∨ (¬ p2839))
    (h73428 : p3585 ∨ p3367)
    (h73846 : p4948 ∨ p2982)
    (h68851 : (¬ p4876) ∨ (¬ p2972) ∨ (¬ p3585) ∨ (¬ p4884) ∨ (¬ p4948))
    : (¬ p2972) ∨ (¬ p2839) ∨ p3367 ∨ p2982 ∨ (¬ p4884) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4884 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4876 := (Or.elim h73804 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u6 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h68851 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step103121 (p2274 p2440 p2563 p2630 p2810 p3097 p4110 p4790 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73516 : p4110 ∨ p2563)
    (h73316 : p2810 ∨ p2630)
    (h69022 : (¬ p2810) ∨ (¬ p2440) ∨ (¬ p4790) ∨ (¬ p4110) ∨ (¬ p3097))
    : (¬ p2440) ∨ p2274 ∨ p2563 ∨ p2630 ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69022 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step103122 (p2192 p2440 p2563 p4110 p4173 p4814 : Prop)
    (h73527 : (¬ p2192) ∨ (¬ p4173))
    (h73516 : p4110 ∨ p2563)
    (h69039 : p4173 ∨ (¬ p4814) ∨ (¬ p2440) ∨ (¬ p4110))
    : (¬ p2192) ∨ (¬ p4814) ∨ p2563 ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4173) := (Or.elim h73527 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h69039 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step103123 (p2177 p2440 p2563 p2881 p3051 p3556 p3570 p4110 p4204 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73516 : p4110 ∨ p2563)
    (h73414 : p3556 ∨ p3051)
    (h69026 : (¬ p3570) ∨ (¬ p2177) ∨ (¬ p3556) ∨ (¬ p2440) ∨ (¬ p4110) ∨ (¬ p4204))
    : p2881 ∨ (¬ p4204) ∨ (¬ p2440) ∨ (¬ p2177) ∨ p2563 ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u8 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h69026 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step103124 (p2230 p2440 p2630 p2810 p4790 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h68522 : (¬ p2440) ∨ (¬ p2230) ∨ (¬ p2810) ∨ (¬ p4790))
    : (¬ p2230) ∨ p2630 ∨ (¬ p4790) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2630) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h68522 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step103128 (p2264 p2437 p2440 p2459 p2659 p3389 p3540 p3575 p4651 p5197 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h73690 : p4651 ∨ (¬ p2437))
    (h69408 : (¬ p4651) ∨ (¬ p3575) ∨ (¬ p5197) ∨ (¬ p3540) ∨ (¬ p2264) ∨ (¬ p2440) ∨ (¬ p2659) ∨ (¬ p2459))
    : (¬ p2440) ∨ (¬ p5197) ∨ p3389 ∨ (¬ p3575) ∨ (¬ p2459) ∨ (¬ p2437) ∨ (¬ p2264) ∨ (¬ p2659) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p4651 := (Or.elim h73690 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    (Or.elim h69408 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step103131 (p2437 p3016 p3574 p3581 p4651 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73690 : p4651 ∨ (¬ p2437))
    (h69008 : (¬ p4651) ∨ (¬ p3574) ∨ (¬ p3581))
    : p3016 ∨ (¬ p3581) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3016) := (fun h => hn (Or.inl h));
    let u1 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p4651 := (Or.elim h73690 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h69008 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step103137 (p2829 p2839 p3319 p3367 p3564 p3583 p3585 p4137 p4868 p5224 : Prop)
    (h73800 : p4868 ∨ (¬ p2829))
    (h73524 : p4137 ∨ p3564)
    (h73428 : p3585 ∨ p3367)
    (h73424 : p3583 ∨ p2839)
    (h69441 : (¬ p4868) ∨ (¬ p4137) ∨ (¬ p3583) ∨ (¬ p3319) ∨ (¬ p5224) ∨ (¬ p3585))
    : (¬ p2829) ∨ (¬ p3319) ∨ p3564 ∨ (¬ p5224) ∨ p3367 ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5224 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4868 := (Or.elim h73800 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u7 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h69441 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u8)))))))))))))

theorem step103141 (p2230 p2589 p2696 p2850 p4749 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h69262 : (¬ p2850) ∨ (¬ p2589) ∨ (¬ p4749) ∨ (¬ p2696))
    : (¬ p2850) ∨ (¬ p4749) ∨ (¬ p2696) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69262 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step103145 (p2274 p2373 p2504 p2553 p3097 p3660 p3880 p4338 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73490 : p3880 ∨ p2373)
    (h69434 : (¬ p2553) ∨ (¬ p3880) ∨ (¬ p2504) ∨ (¬ p4338) ∨ (¬ p3660) ∨ (¬ p3097))
    : (¬ p2553) ∨ p2274 ∨ (¬ p4338) ∨ p2373 ∨ (¬ p3660) ∨ (¬ p2504) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69434 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step103147 (p2230 p2563 p2573 p2579 p3051 p4537 p4558 p4714 : Prop)
    (h73624 : p4537 ∨ (¬ p2230))
    (h73274 : p2579 ∨ p2573)
    (h73720 : p4714 ∨ p2563)
    (h68728 : (¬ p2579) ∨ (¬ p3051) ∨ (¬ p4537) ∨ (¬ p4714) ∨ (¬ p4558))
    : (¬ p3051) ∨ (¬ p2230) ∨ (¬ p4558) ∨ p2573 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4537 := (Or.elim h73624 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4714 := (Or.elim h73720 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h68728 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step103149 (p2177 p2311 p2386 p2911 p3125 p3564 p3581 p3644 p3744 p4624 p5201 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h73434 : p3644 ∨ p2911)
    (h69440 : (¬ p3564) ∨ (¬ p3744) ∨ (¬ p5201) ∨ (¬ p3644) ∨ (¬ p2386) ∨ (¬ p2311) ∨ (¬ p3581) ∨ (¬ p4624) ∨ (¬ p2177))
    : (¬ p3564) ∨ p3125 ∨ (¬ p5201) ∨ (¬ p3581) ∨ (¬ p2311) ∨ (¬ p2177) ∨ p2911 ∨ (¬ p4624) ∨ (¬ p2386) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4624 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h69440 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step103156 (p2177 p2295 p2459 p2553 p2630 p2696 p3568 p4067 p4973 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h69383 : (¬ p2553) ∨ (¬ p4973) ∨ (¬ p3568) ∨ (¬ p4067) ∨ (¬ p2630) ∨ (¬ p2177) ∨ (¬ p2459) ∨ (¬ p2696))
    : (¬ p2553) ∨ (¬ p4067) ∨ (¬ p2177) ∨ p2295 ∨ (¬ p4973) ∨ (¬ p2696) ∨ (¬ p2459) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69383 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step103157 (p2696 p2870 p2901 p3425 p4893 p4906 : Prop)
    (h73814 : p4893 ∨ p2870)
    (h69425 : (¬ p4893) ∨ (¬ p3425) ∨ (¬ p2901) ∨ (¬ p4906) ∨ (¬ p2696))
    : (¬ p3425) ∨ (¬ p2901) ∨ p2870 ∨ (¬ p4906) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3425 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4893 := (Or.elim h73814 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h69425 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step103159 (p2417 p2870 p3246 p3690 p3741 p4244 p4283 p4882 p4988 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73446 : p3690 ∨ p3246)
    (h72406 : (¬ p3690) ∨ (¬ p2417) ∨ (¬ p4283) ∨ (¬ p3741) ∨ (¬ p4882) ∨ (¬ p4244) ∨ (¬ p4988))
    : p2870 ∨ p3246 ∨ (¬ p2417) ∨ (¬ p4882) ∨ (¬ p4283) ∨ (¬ p4988) ∨ (¬ p3741) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4882 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h72406 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step103160 (p2437 p2440 p2870 p4244 p4882 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h69404 : (¬ p2437) ∨ (¬ p4244) ∨ (¬ p2440) ∨ (¬ p4882))
    : p2870 ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p4882) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4882 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h69404 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step103162 (p2187 p2396 p3246 p3872 p3989 p4107 p4356 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73502 : p3989 ∨ p2187)
    (h72408 : (¬ p3246) ∨ (¬ p4107) ∨ (¬ p4356) ∨ (¬ p3872) ∨ (¬ p3989))
    : (¬ p3246) ∨ p2396 ∨ p2187 ∨ (¬ p3872) ∨ (¬ p4356) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h72408 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step103163 (p2156 p2177 p2299 p2319 p2396 p2427 p2563 p2911 p3246 p3741 p4484 p4533 : Prop)
    (h73594 : p4484 ∨ p2156)
    (h73234 : p2299 ∨ p2177)
    (h68643 : (¬ p4484) ∨ (¬ p2911) ∨ (¬ p2319) ∨ (¬ p2396) ∨ (¬ p3246) ∨ (¬ p4533) ∨ (¬ p2299) ∨ (¬ p3741) ∨ (¬ p2427) ∨ (¬ p2563))
    : (¬ p2319) ∨ (¬ p2911) ∨ (¬ p2563) ∨ (¬ p2427) ∨ (¬ p3741) ∨ (¬ p3246) ∨ (¬ p2396) ∨ p2156 ∨ p2177 ∨ (¬ p4533) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4484 := (Or.elim h73594 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u11 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h68643 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step103166 (p2230 p2440 p2441 p2589 p2665 p2685 p2696 p2881 p3005 p3051 p3256 p3379 p3389 p3556 p3570 p4031 p4668 p4669 p4733 p4814 p5189 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73948 : p5189 ∨ p3379)
    (h73418 : p3570 ∨ p2881)
    (h73283 : (¬ p2230) ∨ (¬ p2589))
    (h68503 : (¬ p5189) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p2685) ∨ (¬ p3389) ∨ p2589 ∨ (¬ p4031) ∨ (¬ p2441) ∨ (¬ p3570) ∨ (¬ p3556) ∨ (¬ p4669) ∨ (¬ p4668) ∨ (¬ p2665) ∨ (¬ p4814) ∨ (¬ p2440) ∨ (¬ p2696) ∨ (¬ p4733))
    : (¬ p3256) ∨ (¬ p4814) ∨ (¬ p3005) ∨ (¬ p2696) ∨ (¬ p2441) ∨ (¬ p4031) ∨ (¬ p4733) ∨ p3051 ∨ (¬ p2665) ∨ (¬ p2440) ∨ p3379 ∨ (¬ p3389) ∨ p2881 ∨ (¬ p4668) ∨ (¬ p2685) ∨ (¬ p2230) ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))));
    let u17 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u18 : p5189 := (Or.elim h73948 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    let u19 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u12 r0))));
    let u20 : (¬ p2589) := (Or.elim h73283 (fun q0 => (False.elim (q0 u15))) (fun r0 => r0));
    (Or.elim h68503 (fun q0 => (False.elim (q0 u18))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u14))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u20 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u19))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u17))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u16))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u13))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u8))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u1))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u9))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u3))) (fun r15 => (False.elim (r15 u6)))))))))))))))))))))))))))))))))))

theorem step103170 (p2249 p2437 p2630 p2751 p2810 p2922 p3742 p4281 p4790 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73316 : p2810 ∨ p2630)
    (h68962 : (¬ p3742) ∨ (¬ p4281) ∨ (¬ p2922) ∨ (¬ p2249) ∨ (¬ p2810) ∨ (¬ p4790) ∨ (¬ p2751))
    : (¬ p2922) ∨ p2437 ∨ (¬ p4281) ∨ (¬ p2249) ∨ (¬ p4790) ∨ (¬ p2751) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h68962 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step103178 (p2098 p2177 p2241 p2245 p2247 p2249 p2274 p2363 p2563 p2608 p2727 p2737 p2747 p3367 p3487 p4281 p4500 p4557 p4602 p4714 p4732 p4814 p5215 : Prop)
    (h73302 : p2747 ∨ (¬ p2737))
    (h73720 : p4714 ∨ p2563)
    (h73732 : p4732 ∨ p2608)
    (h73226 : p2247 ∨ p2241)
    (h73636 : p4557 ∨ (¬ p2274))
    (h73962 : p5215 ∨ (¬ p3367))
    (h73602 : p4500 ∨ p2177)
    (h73662 : p4602 ∨ (¬ p2363))
    (h68799 : (¬ p5215) ∨ (¬ p4814) ∨ (¬ p2727) ∨ (¬ p4281) ∨ (¬ p3487) ∨ (¬ p4714) ∨ (¬ p2249) ∨ (¬ p2247) ∨ (¬ p2245) ∨ (¬ p4500) ∨ p2098 ∨ (¬ p4557) ∨ (¬ p2747) ∨ (¬ p4732) ∨ (¬ p4602))
    : p2098 ∨ (¬ p2245) ∨ (¬ p3487) ∨ (¬ p2737) ∨ (¬ p4281) ∨ p2563 ∨ p2608 ∨ p2241 ∨ (¬ p2274) ∨ (¬ p2249) ∨ (¬ p3367) ∨ (¬ p4814) ∨ p2177 ∨ (¬ p2363) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))));
    let u15 : p2747 := (Or.elim h73302 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u16 : p4714 := (Or.elim h73720 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u17 : p4732 := (Or.elim h73732 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u18 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u19 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u8))));
    let u20 : p5215 := (Or.elim h73962 (fun q0 => q0) (fun r0 => (False.elim (r0 u10))));
    let u21 : p4500 := (Or.elim h73602 (fun q0 => q0) (fun r0 => (False.elim (u12 r0))));
    let u22 : p4602 := (Or.elim h73662 (fun q0 => q0) (fun r0 => (False.elim (r0 u13))));
    (Or.elim h68799 (fun q0 => (False.elim (q0 u20))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u14))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u16))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u18))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u21))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (u0 q10))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u19))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u15))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u17))) (fun r13 => (False.elim (r13 u22)))))))))))))))))))))))))))))))

theorem step103179 (p2210 p2440 p3379 p3452 p4814 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h69095 : (¬ p3452) ∨ (¬ p2440) ∨ (¬ p4814) ∨ (¬ p2210))
    : p3379 ∨ (¬ p2210) ∨ (¬ p4814) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h69095 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step103181 (p2187 p2331 p2797 p3005 p3877 p4564 p4584 p4769 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h68508 : (¬ p3877) ∨ (¬ p2187) ∨ (¬ p4584) ∨ (¬ p2331) ∨ (¬ p2797) ∨ (¬ p4769) ∨ (¬ p4564))
    : p3005 ∨ (¬ p2331) ∨ (¬ p4564) ∨ (¬ p4769) ∨ (¬ p4584) ∨ (¬ p2187) ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4769 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h68508 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step103190 (p2220 p2230 p2440 p2542 p2589 p2619 p2659 p3156 p3413 p3694 p4109 p4750 : Prop)
    (h73450 : p3694 ∨ p2619)
    (h73270 : p2542 ∨ p2440)
    (h73284 : p2589 ∨ p2230)
    (h69232 : (¬ p3694) ∨ (¬ p2220) ∨ (¬ p2589) ∨ (¬ p4109) ∨ (¬ p3156) ∨ (¬ p2659) ∨ (¬ p3413) ∨ (¬ p2542) ∨ (¬ p4750))
    : p2619 ∨ p2440 ∨ (¬ p4750) ∨ (¬ p4109) ∨ (¬ p3413) ∨ (¬ p3156) ∨ p2230 ∨ (¬ p2220) ∨ (¬ p2659) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3694 := (Or.elim h73450 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h69232 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step103196 (p2122 p2274 p2563 p3822 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h68702 : (¬ p3822) ∨ (¬ p2563) ∨ (¬ p2274))
    : (¬ p2274) ∨ p2122 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h68702 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u0)))))))

theorem step103197 (p2132 p2138 p2427 p2850 p2881 p3379 p3452 p3570 p4235 p4880 p5217 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73806 : p4880 ∨ p2850)
    (h73394 : p3452 ∨ p3379)
    (h73418 : p3570 ∨ p2881)
    (h73536 : p4235 ∨ p2427)
    (h68785 : (¬ p4235) ∨ (¬ p2138) ∨ (¬ p3570) ∨ (¬ p4880) ∨ (¬ p3452) ∨ (¬ p5217))
    : p2132 ∨ p2850 ∨ (¬ p5217) ∨ p3379 ∨ p2881 ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5217 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4880 := (Or.elim h73806 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h68785 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step103199 (p2132 p2138 p2440 p2542 p2696 p2850 p3684 p4750 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73270 : p2542 ∨ p2440)
    (h73442 : p3684 ∨ p2850)
    (h68805 : (¬ p2542) ∨ (¬ p3684) ∨ (¬ p2138) ∨ (¬ p4750) ∨ (¬ p2696))
    : p2132 ∨ p2440 ∨ (¬ p4750) ∨ (¬ p2696) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h68805 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step103200 (p2246 p2946 p2956 p2992 p3662 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73334 : p2956 ∨ (¬ p2946))
    (h69287 : (¬ p2956) ∨ (¬ p3662) ∨ (¬ p2246))
    : p2992 ∨ (¬ p2246) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p2956 := (Or.elim h73334 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h69287 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step103201 (p2246 p2685 p2751 p2901 p2946 p2956 p3051 p3572 p4916 : Prop)
    (h73826 : p4916 ∨ p2901)
    (h73420 : p3572 ∨ p2685)
    (h73334 : p2956 ∨ (¬ p2946))
    (h69418 : (¬ p4916) ∨ (¬ p3051) ∨ (¬ p3572) ∨ (¬ p2956) ∨ (¬ p2246) ∨ (¬ p2751))
    : (¬ p3051) ∨ p2901 ∨ (¬ p2246) ∨ p2685 ∨ (¬ p2751) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4916 := (Or.elim h73826 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p2956 := (Or.elim h73334 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    (Or.elim h69418 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step103206 (p2850 p2901 p3096 p3201 p3422 p3584 p4705 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h68379 : (¬ p2850) ∨ p3201 ∨ (¬ p3584) ∨ (¬ p2901) ∨ (¬ p4705) ∨ (¬ p3096))
    : p3201 ∨ (¬ p2901) ∨ (¬ p4705) ∨ (¬ p3096) ∨ (¬ p2850) ∨ p3422 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h68379 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step103207 (p2246 p2331 p2641 p4755 : Prop)
    (h73744 : p4755 ∨ p2641)
    (h68481 : (¬ p4755) ∨ (¬ p2331) ∨ (¬ p2246))
    : p2641 ∨ (¬ p2246) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4755 := (Or.elim h73744 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h68481 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u1)))))))

theorem step103220 (p2088 p2363 p2459 p2608 p2696 p2737 p2747 p4602 p4667 p4732 p4788 : Prop)
    (h73732 : p4732 ∨ p2608)
    (h73662 : p4602 ∨ (¬ p2363))
    (h73302 : p2747 ∨ (¬ p2737))
    (h73760 : p4788 ∨ (¬ p2696))
    (h73698 : p4667 ∨ (¬ p2459))
    (h69451 : (¬ p4667) ∨ (¬ p4788) ∨ (¬ p2747) ∨ (¬ p2088) ∨ (¬ p4732) ∨ (¬ p4602))
    : p2608 ∨ (¬ p2363) ∨ (¬ p2737) ∨ (¬ p2696) ∨ (¬ p2088) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4732 := (Or.elim h73732 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4602 := (Or.elim h73662 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u8 : p2747 := (Or.elim h73302 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u9 : p4788 := (Or.elim h73760 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u10 : p4667 := (Or.elim h73698 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    (Or.elim h69451 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step103224 (p2132 p2138 p2187 p2363 p2774 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h68726 : (¬ p2774) ∨ (¬ p2138) ∨ (¬ p2187) ∨ (¬ p2363))
    : (¬ p2774) ∨ p2132 ∨ (¬ p2363) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2774 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h68726 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step103226 (p2098 p2104 p2122 p2774 p2829 : Prop)
    (h73204 : p2104 ∨ p2098)
    (h72437 : (¬ p2104) ∨ (¬ p2829) ∨ (¬ p2774) ∨ (¬ p2122))
    : p2098 ∨ (¬ p2122) ∨ (¬ p2829) ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h72437 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step103227 (p2122 p2274 p2363 p2630 p2668 p2785 p2786 p3822 p4389 p4841 p4972 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h68514 : (¬ p2668) ∨ (¬ p4841) ∨ (¬ p3822) ∨ (¬ p2786) ∨ (¬ p2785) ∨ (¬ p2630) ∨ (¬ p4972) ∨ (¬ p4389) ∨ (¬ p2274) ∨ (¬ p2363))
    : (¬ p2668) ∨ (¬ p4841) ∨ (¬ p4389) ∨ p2122 ∨ (¬ p2786) ∨ (¬ p2274) ∨ (¬ p2785) ∨ (¬ p2630) ∨ (¬ p2363) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4841 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h68514 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step103229 (p2166 p2220 p2246 p2619 p2630 p2751 p3136 p3694 p4315 p4392 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73450 : p3694 ∨ p2619)
    (h69734 : (¬ p4315) ∨ (¬ p4392) ∨ (¬ p2246) ∨ (¬ p3694) ∨ (¬ p2220) ∨ (¬ p2166) ∨ (¬ p2630) ∨ (¬ p2751))
    : (¬ p2751) ∨ p3136 ∨ (¬ p4392) ∨ (¬ p2220) ∨ (¬ p2166) ∨ (¬ p2630) ∨ (¬ p2246) ∨ p2619 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2751 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3136) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3694 := (Or.elim h73450 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h69734 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step103236 (p2341 p2427 p2590 p2901 p2911 p3370 p3581 p3644 p4235 p4632 p4705 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73536 : p4235 ∨ p2427)
    (h68990 : (¬ p2901) ∨ (¬ p4632) ∨ (¬ p2341) ∨ (¬ p3644) ∨ (¬ p3370) ∨ (¬ p4705) ∨ (¬ p3581) ∨ (¬ p4235) ∨ (¬ p2590))
    : (¬ p2901) ∨ (¬ p3370) ∨ (¬ p2341) ∨ (¬ p2590) ∨ p2911 ∨ (¬ p3581) ∨ p2427 ∨ (¬ p4632) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h68990 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step103241 (p2166 p2177 p2191 p2210 p2274 p3097 p3399 p3555 p4500 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73352 : p3097 ∨ p2274)
    (h73602 : p4500 ∨ p2177)
    (h73222 : p2191 ∨ p2166)
    (h69130 : (¬ p2191) ∨ (¬ p3399) ∨ (¬ p4500) ∨ (¬ p3555) ∨ (¬ p3097))
    : (¬ p3399) ∨ p2210 ∨ p2274 ∨ p2177 ∨ p2166 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4500 := (Or.elim h73602 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p2191 := (Or.elim h73222 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h69130 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step103242 (p2166 p2177 p2191 p2192 p2881 p4556 p4900 : Prop)
    (h73222 : p2191 ∨ p2166)
    (h73818 : p4900 ∨ p2881)
    (h69078 : (¬ p4900) ∨ (¬ p2191) ∨ (¬ p2177) ∨ (¬ p2192) ∨ (¬ p4556))
    : (¬ p2192) ∨ p2166 ∨ (¬ p4556) ∨ (¬ p2177) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2191 := (Or.elim h73222 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4900 := (Or.elim h73818 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h69078 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step103243 (p2166 p2177 p2191 p2192 p2210 p2274 p2608 p3073 p3954 p4554 : Prop)
    (h73222 : p2191 ∨ p2166)
    (h73634 : p4554 ∨ p2274)
    (h73498 : p3954 ∨ p2608)
    (h69108 : (¬ p2192) ∨ (¬ p2177) ∨ (¬ p3073) ∨ (¬ p2191) ∨ (¬ p2210) ∨ (¬ p4554) ∨ (¬ p3954))
    : (¬ p2192) ∨ p2166 ∨ p2274 ∨ (¬ p2210) ∨ p2608 ∨ (¬ p3073) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2191 := (Or.elim h73222 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4554 := (Or.elim h73634 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h69108 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (False.elim (r5 u9)))))))))))))))

theorem step103244 (p2166 p2191 p2406 p2493 p2563 p4627 p4716 : Prop)
    (h73222 : p2191 ∨ p2166)
    (h73722 : p4716 ∨ (¬ p2563))
    (h73676 : p4627 ∨ p2406)
    (h69557 : (¬ p2191) ∨ (¬ p2493) ∨ (¬ p4627) ∨ (¬ p4716))
    : p2166 ∨ (¬ p2563) ∨ p2406 ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2166) := (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2191 := (Or.elim h73222 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4716 := (Or.elim h73722 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u6 : p4627 := (Or.elim h73676 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h69557 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step103247 (p2630 p2870 p3051 p3370 p3412 p4244 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h69736 : (¬ p3412) ∨ (¬ p3051) ∨ (¬ p3370) ∨ (¬ p4244) ∨ (¬ p2630))
    : (¬ p3370) ∨ (¬ p3412) ∨ (¬ p3051) ∨ (¬ p2630) ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3370 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h69736 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step103249 (p2264 p2274 p2284 p2298 p2459 p2641 p2881 p3323 p4336 p4554 p4624 : Prop)
    (h73634 : p4554 ∨ p2274)
    (h69389 : (¬ p3323) ∨ (¬ p2284) ∨ (¬ p4336) ∨ (¬ p2264) ∨ (¬ p2881) ∨ (¬ p2298) ∨ (¬ p2641) ∨ (¬ p4624) ∨ (¬ p2459) ∨ (¬ p4554))
    : (¬ p2641) ∨ (¬ p3323) ∨ (¬ p2298) ∨ (¬ p2264) ∨ p2274 ∨ (¬ p4624) ∨ (¬ p2881) ∨ (¬ p4336) ∨ (¬ p2459) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2298 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4624 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4554 := (Or.elim h73634 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h69389 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u10)))))))))))))))))))))

theorem step103250 (p2528 p2534 p2563 p3146 p5057 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73898 : p5057 ∨ (¬ p3146))
    (h69461 : (¬ p5057) ∨ (¬ p2534) ∨ (¬ p2563))
    : p2528 ∨ (¬ p3146) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p5057 := (Or.elim h73898 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h69461 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step103253 (p2177 p2187 p2264 p2274 p3553 p3989 p4500 : Prop)
    (h73409 : (¬ p2264) ∨ (¬ p3553))
    (h73502 : p3989 ∨ p2187)
    (h73602 : p4500 ∨ p2177)
    (h68692 : p3553 ∨ (¬ p3989) ∨ (¬ p4500) ∨ (¬ p2274))
    : (¬ p2264) ∨ (¬ p2274) ∨ p2187 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3553) := (Or.elim h73409 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u5 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4500 := (Or.elim h73602 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h68692 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step103255 (p2132 p2753 p2774 p2780 p2850 p3201 p3876 p4644 p4715 p4883 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73486 : p3876 ∨ p3201)
    (h73808 : p4883 ∨ (¬ p2850))
    (h68722 : (¬ p4883) ∨ (¬ p3876) ∨ (¬ p4644) ∨ (¬ p2780) ∨ (¬ p2132) ∨ (¬ p4715) ∨ (¬ p2753))
    : p2774 ∨ (¬ p2132) ∨ p3201 ∨ (¬ p2850) ∨ (¬ p2753) ∨ (¬ p4715) ∨ (¬ p4644) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p4883 := (Or.elim h73808 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h68722 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step103258 (p2166 p2619 p2751 p2992 p3136 p3694 p4315 p4392 p4958 : Prop)
    (h73852 : p4958 ∨ (¬ p2992))
    (h73450 : p3694 ∨ p2619)
    (h73550 : p4315 ∨ p3136)
    (h69198 : (¬ p4958) ∨ (¬ p2166) ∨ (¬ p3694) ∨ (¬ p4392) ∨ (¬ p4315) ∨ (¬ p2751))
    : (¬ p2992) ∨ p2619 ∨ (¬ p2751) ∨ (¬ p2166) ∨ p3136 ∨ (¬ p4392) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4958 := (Or.elim h73852 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u7 : p3694 := (Or.elim h73450 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h69198 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step103259 (p2230 p2440 p2630 p2751 p2850 p2992 p3684 p4703 p4748 p4790 : Prop)
    (h73740 : p4748 ∨ p2630)
    (h73714 : p4703 ∨ p2440)
    (h73442 : p3684 ∨ p2850)
    (h68369 : (¬ p3684) ∨ (¬ p2230) ∨ (¬ p2992) ∨ (¬ p4748) ∨ (¬ p4703) ∨ (¬ p4790) ∨ (¬ p2751))
    : (¬ p2992) ∨ p2630 ∨ (¬ p2751) ∨ (¬ p4790) ∨ p2440 ∨ (¬ p2230) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2630) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4748 := (Or.elim h73740 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4703 := (Or.elim h73714 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h68369 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step103260 (p2440 p2727 p2922 p2928 p2992 p4644 p4703 p4809 : Prop)
    (h73770 : p4809 ∨ p2727)
    (h73320 : p2928 ∨ p2922)
    (h73714 : p4703 ∨ p2440)
    (h68948 : (¬ p4809) ∨ (¬ p2928) ∨ (¬ p2992) ∨ (¬ p4703) ∨ (¬ p4644))
    : p2727 ∨ (¬ p2992) ∨ p2922 ∨ (¬ p4644) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4809 := (Or.elim h73770 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4703 := (Or.elim h73714 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h68948 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step103263 (p2245 p2295 p2553 p2588 p2630 p2641 p2727 p2810 p3568 p4154 p4790 p4976 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73282 : p2588 ∨ p2553)
    (h73316 : p2810 ∨ p2630)
    (h73416 : p3568 ∨ p2295)
    (h69371 : (¬ p4154) ∨ (¬ p2727) ∨ (¬ p3568) ∨ (¬ p2245) ∨ (¬ p4976) ∨ (¬ p2588) ∨ (¬ p2810) ∨ (¬ p4790))
    : p2641 ∨ (¬ p2727) ∨ p2553 ∨ p2630 ∨ (¬ p2245) ∨ (¬ p4790) ∨ (¬ p4976) ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4976 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h69371 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step103264 (p2951 p3051 p3156 p3246 p3497 p4668 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h69310 : (¬ p2951) ∨ (¬ p3497) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p4668))
    : (¬ p3246) ∨ (¬ p2951) ∨ (¬ p3051) ∨ p3156 ∨ (¬ p4668) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69310 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step103265 (p2088 p2651 p2657 p3256 p5011 p5106 : Prop)
    (h73922 : p5106 ∨ p3256)
    (h73288 : p2657 ∨ p2651)
    (h68884 : (¬ p5106) ∨ (¬ p2657) ∨ (¬ p5011) ∨ (¬ p2088))
    : p3256 ∨ (¬ p2088) ∨ p2651 ∨ (¬ p5011) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5011 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5106 := (Or.elim h73922 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h68884 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step103267 (p2156 p2187 p2331 p2668 p3646 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h68542 : p2187 ∨ (¬ p3646) ∨ p2331 ∨ (¬ p2668))
    : (¬ p2668) ∨ p2331 ∨ p2187 ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h68542 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step103271 (p2192 p2284 p2727 p4511 : Prop)
    (h73610 : p4511 ∨ p2192)
    (h69741 : (¬ p4511) ∨ (¬ p2727) ∨ (¬ p2284))
    : (¬ p2284) ∨ (¬ p2727) ∨ p2192 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4511 := (Or.elim h73610 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h69741 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step103273 (p2249 p2274 p2295 p2307 p2313 p2807 p2996 p3027 p3097 p4560 p4571 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73352 : p3097 ∨ p2274)
    (h73644 : p4571 ∨ (¬ p2295))
    (h73340 : p3027 ∨ p2996)
    (h72955 : p4560)
    (h69138 : (¬ p4571) ∨ (¬ p2313) ∨ p2807 ∨ (¬ p3027) ∨ (¬ p2249) ∨ (¬ p4560) ∨ (¬ p3097))
    : p2307 ∨ p2274 ∨ (¬ p2295) ∨ (¬ p2249) ∨ p2996 ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2307) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4571 := (Or.elim h73644 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    let u9 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4560 := h72955;
    (Or.elim h69138 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (False.elim (r5 u7)))))))))))))))

theorem step103276 (p2210 p2406 p2608 p2850 p3684 p3954 p4630 p5217 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73678 : p4630 ∨ (¬ p2406))
    (h73442 : p3684 ∨ p2850)
    (h68905 : (¬ p3684) ∨ (¬ p4630) ∨ (¬ p2210) ∨ (¬ p5217) ∨ (¬ p3954))
    : p2608 ∨ (¬ p2406) ∨ (¬ p2210) ∨ (¬ p5217) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5217 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4630 := (Or.elim h73678 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u7 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h68905 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step103290 (p2274 p3093 p3097 p3399 p4518 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h69131 : p3093 ∨ (¬ p3399) ∨ (¬ p4518) ∨ (¬ p3097))
    : p3093 ∨ (¬ p3399) ∨ p2274 ∨ (¬ p4518) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h69131 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step103292 (p2177 p2241 p2247 p2274 p2363 p2641 p3097 p3146 p3309 p3549 p3692 p4500 p4755 : Prop)
    (h73744 : p4755 ∨ p2641)
    (h73226 : p2247 ∨ p2241)
    (h73406 : p3549 ∨ p3309)
    (h73448 : p3692 ∨ p3146)
    (h73352 : p3097 ∨ p2274)
    (h73602 : p4500 ∨ p2177)
    (h69259 : (¬ p4755) ∨ (¬ p3692) ∨ (¬ p2247) ∨ (¬ p3549) ∨ (¬ p4500) ∨ (¬ p3097) ∨ (¬ p2363))
    : p2641 ∨ p2241 ∨ p3309 ∨ p3146 ∨ (¬ p2363) ∨ p2274 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4755 := (Or.elim h73744 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p4500 := (Or.elim h73602 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h69259 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step103294 (p2177 p2299 p2373 p2406 p2563 p3238 p3309 p3379 p3452 p3549 p3880 p4716 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73394 : p3452 ∨ p3379)
    (h73234 : p2299 ∨ p2177)
    (h73406 : p3549 ∨ p3309)
    (h73374 : p3238 ∨ p2406)
    (h73722 : p4716 ∨ (¬ p2563))
    (h69583 : (¬ p3238) ∨ (¬ p3549) ∨ (¬ p3452) ∨ (¬ p3880) ∨ (¬ p2299) ∨ (¬ p4716))
    : p2373 ∨ p3379 ∨ p2177 ∨ p3309 ∨ p2406 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2373) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p4716 := (Or.elim h73722 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    (Or.elim h69583 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (False.elim (r4 u11)))))))))))))

theorem step103296 (p2363 p3146 p3323 p3692 p3988 p4433 p4560 p4602 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h72955 : p4560)
    (h73662 : p4602 ∨ (¬ p2363))
    (h69433 : (¬ p3692) ∨ (¬ p4560) ∨ (¬ p4433) ∨ (¬ p3323) ∨ (¬ p3988) ∨ (¬ p4602))
    : (¬ p3323) ∨ p3146 ∨ (¬ p3988) ∨ (¬ p4433) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4560 := h72955;
    let u7 : p4602 := (Or.elim h73662 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    (Or.elim h69433 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step103301 (p2363 p2563 p2598 p2850 p3146 p3266 p4433 p5055 : Prop)
    (h73896 : p5055 ∨ p3146)
    (h69126 : (¬ p5055) ∨ (¬ p3266) ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p4433) ∨ (¬ p2563) ∨ (¬ p2363))
    : p3146 ∨ (¬ p3266) ∨ (¬ p2563) ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p4433) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5055 := (Or.elim h73896 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h69126 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step103308 (p2132 p2440 p2493 p2590 p2696 p2737 p2774 p2780 p3083 p3365 p3367 p4256 p4608 p5217 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h73542 : p4256 ∨ p3083)
    (h73308 : p2780 ∨ p2774)
    (h68798 : (¬ p2132) ∨ (¬ p2780) ∨ (¬ p2493) ∨ (¬ p2440) ∨ (¬ p4256) ∨ (¬ p4608) ∨ (¬ p3365) ∨ (¬ p5217) ∨ (¬ p3367) ∨ (¬ p2590) ∨ (¬ p2737))
    : p2696 ∨ (¬ p2132) ∨ p3083 ∨ (¬ p3367) ∨ (¬ p2590) ∨ (¬ p4608) ∨ (¬ p2737) ∨ (¬ p2493) ∨ p2774 ∨ (¬ p5217) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2696) := (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5217 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u13 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h68798 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u4))) (fun r9 => (False.elim (r9 u6)))))))))))))))))))))))

theorem step103315 (p2098 p2132 p2135 p2220 p4120 : Prop)
    (h73212 : p2135 ∨ p2132)
    (h73522 : p4120 ∨ p2220)
    (h68650 : (¬ p2135) ∨ (¬ p4120) ∨ (¬ p2098))
    : (¬ p2098) ∨ p2132 ∨ p2220 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2135 := (Or.elim h73212 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h68650 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u0)))))))

theorem step103316 (p2098 p2696 p2737 p3256 p3365 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h68552 : (¬ p3365) ∨ (¬ p3256) ∨ (¬ p2098) ∨ (¬ p2737))
    : (¬ p2098) ∨ p2696 ∨ (¬ p3256) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h68552 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step103320 (p2192 p2440 p2563 p2641 p2727 p4110 p4111 p4173 p4703 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73527 : (¬ p2192) ∨ (¬ p4173))
    (h73516 : p4110 ∨ p2563)
    (h73714 : p4703 ∨ p2440)
    (h68889 : (¬ p4111) ∨ p4173 ∨ (¬ p2641) ∨ (¬ p4703) ∨ (¬ p4110))
    : p2727 ∨ (¬ p2641) ∨ (¬ p2192) ∨ p2563 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : (¬ p4173) := (Or.elim h73527 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p4703 := (Or.elim h73714 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h68889 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step103321 (p2641 p2727 p2737 p2747 p3367 p3585 p4111 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h73518 : p4111 ∨ p2727)
    (h73302 : p2747 ∨ (¬ p2737))
    (h69449 : (¬ p2641) ∨ (¬ p4111) ∨ (¬ p3585) ∨ (¬ p2747))
    : (¬ p2641) ∨ p3367 ∨ p2727 ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3367) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2747 := (Or.elim h73302 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h69449 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step103325 (p2230 p2246 p2406 p2589 p2641 p2727 p3016 p3238 p4717 p4809 p4974 : Prop)
    (h73860 : p4974 ∨ (¬ p3016))
    (h73284 : p2589 ∨ p2230)
    (h73374 : p3238 ∨ p2406)
    (h73770 : p4809 ∨ p2727)
    (h69212 : (¬ p4809) ∨ (¬ p4974) ∨ (¬ p2641) ∨ (¬ p2246) ∨ (¬ p2589) ∨ (¬ p3238) ∨ (¬ p4717))
    : (¬ p2246) ∨ (¬ p2641) ∨ (¬ p4717) ∨ (¬ p3016) ∨ p2230 ∨ p2406 ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4974 := (Or.elim h73860 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u8 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p4809 := (Or.elim h73770 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h69212 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step103326 (p2230 p2241 p2246 p2247 p2406 p2553 p2588 p2589 p2641 p2727 p3238 p4717 p4809 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h73770 : p4809 ∨ p2727)
    (h73282 : p2588 ∨ p2553)
    (h73226 : p2247 ∨ p2241)
    (h73284 : p2589 ∨ p2230)
    (h69348 : (¬ p4809) ∨ (¬ p2641) ∨ (¬ p2589) ∨ (¬ p3238) ∨ (¬ p2247) ∨ (¬ p2246) ∨ (¬ p2588) ∨ (¬ p4717))
    : (¬ p2246) ∨ (¬ p2641) ∨ p2406 ∨ p2727 ∨ (¬ p4717) ∨ p2553 ∨ p2241 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p4809 := (Or.elim h73770 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h69348 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step103331 (p2177 p2210 p2299 p2373 p2406 p2563 p3238 p3309 p3549 p3555 p3880 p4034 p4516 p4716 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73234 : p2299 ∨ p2177)
    (h73722 : p4716 ∨ (¬ p2563))
    (h73490 : p3880 ∨ p2373)
    (h73406 : p3549 ∨ p3309)
    (h73374 : p3238 ∨ p2406)
    (h69589 : (¬ p4034) ∨ (¬ p3238) ∨ (¬ p3549) ∨ (¬ p3880) ∨ (¬ p4516) ∨ (¬ p2299) ∨ (¬ p3555) ∨ (¬ p4716))
    : p2210 ∨ (¬ p4516) ∨ p2177 ∨ (¬ p2563) ∨ p2373 ∨ p3309 ∨ (¬ p4034) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : p4516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4034 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4716 := (Or.elim h73722 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u11 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h69589 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u10)))))))))))))))))

theorem step103341 (p2241 p2247 p2264 p2437 p2727 p3553 p3742 p4111 p4112 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73518 : p4111 ∨ p2727)
    (h73410 : p3553 ∨ p2264)
    (h73452 : p3742 ∨ p2437)
    (h68685 : (¬ p4111) ∨ (¬ p3553) ∨ (¬ p3742) ∨ (¬ p4112) ∨ (¬ p2247))
    : p2241 ∨ p2727 ∨ p2264 ∨ (¬ p4112) ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4112 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h68685 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step103343 (p2363 p2373 p2982 p4433 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h68919 : (¬ p2373) ∨ (¬ p4948) ∨ (¬ p4433) ∨ (¬ p2363))
    : p2982 ∨ (¬ p2363) ∨ (¬ p4433) ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h68919 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step103345 (p2156 p2220 p2341 p2881 p3551 p4527 p4555 p4903 : Prop)
    (h73618 : p4527 ∨ p2220)
    (h73408 : p3551 ∨ p2341)
    (h73820 : p4903 ∨ (¬ p2881))
    (h69094 : (¬ p4903) ∨ (¬ p2156) ∨ (¬ p3551) ∨ (¬ p4527) ∨ (¬ p4555))
    : p2220 ∨ p2341 ∨ (¬ p2156) ∨ (¬ p2881) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2220) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4527 := (Or.elim h73618 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4903 := (Or.elim h73820 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h69094 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step103346 (p2220 p3051 p3747 p4527 : Prop)
    (h73618 : p4527 ∨ p2220)
    (h69454 : (¬ p4527) ∨ (¬ p3051) ∨ (¬ p3747))
    : (¬ p3051) ∨ (¬ p3747) ∨ p2220 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4527 := (Or.elim h73618 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h69454 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step103347 (p2177 p2274 p2299 p2911 p3097 p4718 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73234 : p2299 ∨ p2177)
    (h69101 : (¬ p2299) ∨ (¬ p2911) ∨ (¬ p4718) ∨ (¬ p3097))
    : (¬ p2911) ∨ p2274 ∨ (¬ p4718) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69101 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step103358 (p2363 p2630 p2668 p2696 p2819 p4358 p4972 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h68500 : (¬ p2668) ∨ (¬ p4358) ∨ (¬ p2630) ∨ (¬ p4972) ∨ (¬ p2696) ∨ (¬ p2363))
    : (¬ p2668) ∨ (¬ p4972) ∨ (¬ p2630) ∨ p2819 ∨ (¬ p2363) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h68500 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step103361 (p2122 p2295 p2573 p2579 p3016 p3347 p3822 p4750 p4811 p4974 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73860 : p4974 ∨ (¬ p3016))
    (h73274 : p2579 ∨ p2573)
    (h69180 : (¬ p4974) ∨ (¬ p2579) ∨ (¬ p3347) ∨ (¬ p2295) ∨ (¬ p3822) ∨ (¬ p4811) ∨ (¬ p4750))
    : (¬ p2295) ∨ p2122 ∨ (¬ p3347) ∨ (¬ p4750) ∨ (¬ p4811) ∨ (¬ p3016) ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4974 := (Or.elim h73860 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    let u9 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h69180 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step103364 (p2341 p2608 p3073 p3399 p3954 p5209 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73958 : p5209 ∨ (¬ p3399))
    (h69113 : (¬ p5209) ∨ (¬ p2341) ∨ (¬ p3073) ∨ (¬ p3954))
    : p2608 ∨ (¬ p3073) ∨ (¬ p2341) ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p5209 := (Or.elim h73958 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h69113 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step103365 (p2608 p3073 p3399 p3527 p3954 p5306 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73994 : p5306 ∨ (¬ p3527))
    (h68430 : (¬ p3399) ∨ (¬ p5306) ∨ (¬ p3073) ∨ (¬ p3954))
    : p2608 ∨ (¬ p3073) ∨ (¬ p3527) ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p5306 := (Or.elim h73994 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h68430 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step103369 (p2264 p2341 p2630 p2717 p3553 p3659 p4117 p4357 p4650 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h73409 : (¬ p2264) ∨ (¬ p3553))
    (h69384 : (¬ p3659) ∨ (¬ p2341) ∨ (¬ p4357) ∨ p3553 ∨ (¬ p4650) ∨ (¬ p2630) ∨ (¬ p4117))
    : (¬ p2341) ∨ p2717 ∨ (¬ p2264) ∨ (¬ p2630) ∨ (¬ p4117) ∨ (¬ p4357) ∨ (¬ p4650) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4357 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : (¬ p3553) := (Or.elim h73409 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h69384 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step103374 (p2132 p2138 p2440 p2542 p2598 p4750 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73270 : p2542 ∨ p2440)
    (h68314 : (¬ p2598) ∨ (¬ p4750) ∨ (¬ p2138) ∨ (¬ p2542))
    : p2132 ∨ p2440 ∨ (¬ p2598) ∨ (¬ p4750) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h68314 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step103375 (p2122 p2177 p2363 p2553 p2588 p2598 p3822 p4502 : Prop)
    (h73471 : (¬ p2122) ∨ (¬ p3822))
    (h73282 : p2588 ∨ p2553)
    (h73604 : p4502 ∨ (¬ p2177))
    (h68432 : p3822 ∨ (¬ p2588) ∨ (¬ p2598) ∨ (¬ p4502) ∨ (¬ p2363))
    : (¬ p2122) ∨ p2553 ∨ (¬ p2177) ∨ (¬ p2598) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3822) := (Or.elim h73471 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4502 := (Or.elim h73604 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h68432 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step103376 (p2098 p2104 p2598 p3083 p4750 : Prop)
    (h73204 : p2104 ∨ p2098)
    (h68764 : (¬ p2598) ∨ (¬ p3083) ∨ (¬ p4750) ∨ (¬ p2104))
    : p2098 ∨ (¬ p3083) ∨ (¬ p4750) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h68764 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step103380 (p2274 p2563 p3097 p3309 p3549 p4110 p4632 : Prop)
    (h73405 : (¬ p3309) ∨ (¬ p3549))
    (h73352 : p3097 ∨ p2274)
    (h73516 : p4110 ∨ p2563)
    (h68871 : p3549 ∨ (¬ p4632) ∨ (¬ p4110) ∨ (¬ p3097))
    : (¬ p3309) ∨ p2274 ∨ p2563 ∨ (¬ p4632) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3549) := (Or.elim h73405 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h68871 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step103381 (p2210 p2563 p3093 p4110 p4520 p4632 : Prop)
    (h73614 : p4520 ∨ p2210)
    (h73516 : p4110 ∨ p2563)
    (h68879 : (¬ p4520) ∨ (¬ p3093) ∨ (¬ p4632) ∨ (¬ p4110))
    : (¬ p3093) ∨ p2210 ∨ (¬ p4632) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3093 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4520 := (Or.elim h73614 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h68879 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step103384 (p2440 p3266 p3343 p3506 p4444 p4953 p5174 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73946 : p5174 ∨ (¬ p3343))
    (h68840 : (¬ p5174) ∨ (¬ p4444) ∨ (¬ p3506) ∨ (¬ p4953) ∨ (¬ p2440))
    : (¬ p3506) ∨ p3266 ∨ (¬ p4953) ∨ (¬ p2440) ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p5174 := (Or.elim h73946 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    (Or.elim h68840 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step103394 (p2122 p2352 p2850 p3822 p3955 p4715 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h68287 : (¬ p2352) ∨ (¬ p2850) ∨ (¬ p3822) ∨ (¬ p3955) ∨ (¬ p4715))
    : p2122 ∨ (¬ p2352) ∨ (¬ p2850) ∨ (¬ p3955) ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h68287 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step103395 (p2177 p2341 p3093 p3379 p3399 p3551 p3687 p4870 p5205 : Prop)
    (h73956 : p5205 ∨ p3399)
    (h73408 : p3551 ∨ p2341)
    (h69119 : (¬ p5205) ∨ (¬ p3687) ∨ (¬ p3551) ∨ (¬ p3093) ∨ (¬ p3379) ∨ (¬ p4870) ∨ (¬ p2177))
    : p3399 ∨ (¬ p3687) ∨ (¬ p3093) ∨ (¬ p2177) ∨ (¬ p4870) ∨ (¬ p3379) ∨ p2341 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p3687 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5205 := (Or.elim h73956 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h69119 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step103403 (p2274 p2295 p2992 p2996 p3027 p3097 p3662 p4560 p4571 : Prop)
    (h73644 : p4571 ∨ (¬ p2295))
    (h73440 : p3662 ∨ p2992)
    (h73340 : p3027 ∨ p2996)
    (h73352 : p3097 ∨ p2274)
    (h72955 : p4560)
    (h69165 : (¬ p4571) ∨ (¬ p3027) ∨ (¬ p4560) ∨ (¬ p3662) ∨ (¬ p3097))
    : (¬ p2295) ∨ p2992 ∨ p2996 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4571 := (Or.elim h73644 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p4560 := h72955;
    (Or.elim h69165 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step103404 (p2459 p2727 p2911 p2922 p2996 p3027 p4809 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73770 : p4809 ∨ p2727)
    (h68946 : (¬ p4809) ∨ (¬ p3027) ∨ (¬ p2922) ∨ (¬ p2459) ∨ (¬ p2911))
    : p2996 ∨ (¬ p2911) ∨ (¬ p2922) ∨ p2727 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4809 := (Or.elim h73770 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h68946 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step103409 (p2187 p2274 p2307 p2352 p2493 p3989 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h68842 : (¬ p2352) ∨ (¬ p2493) ∨ (¬ p2307) ∨ (¬ p3989) ∨ (¬ p2274))
    : (¬ p2307) ∨ (¬ p2493) ∨ p2187 ∨ (¬ p2352) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h68842 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step103413 (p2274 p2363 p2459 p2563 p3093 p3097 p3125 p3591 p4348 p4503 p4602 p4632 p4714 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73352 : p3097 ∨ p2274)
    (h73562 : p4348 ∨ p2459)
    (h73662 : p4602 ∨ (¬ p2363))
    (h73720 : p4714 ∨ p2563)
    (h68961 : (¬ p3125) ∨ (¬ p4348) ∨ (¬ p3591) ∨ (¬ p4632) ∨ (¬ p4503) ∨ (¬ p4714) ∨ (¬ p3097) ∨ (¬ p4602))
    : (¬ p3125) ∨ p3093 ∨ p2274 ∨ (¬ p4503) ∨ p2459 ∨ (¬ p2363) ∨ p2563 ∨ (¬ p4632) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p4602 := (Or.elim h73662 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    let u12 : p4714 := (Or.elim h73720 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h68961 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u11)))))))))))))))))

theorem step103414 (p2177 p2230 p2299 p2373 p2459 p2850 p2982 p3093 p3146 p3309 p3367 p3549 p3591 p3692 p4335 p4355 p4420 p4667 p4733 p4902 p5190 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73698 : p4667 ∨ (¬ p2459))
    (h73234 : p2299 ∨ p2177)
    (h73448 : p3692 ∨ p3146)
    (h73406 : p3549 ∨ p3309)
    (h69260 : (¬ p3591) ∨ (¬ p2982) ∨ (¬ p2373) ∨ (¬ p4355) ∨ (¬ p3692) ∨ (¬ p4335) ∨ (¬ p2850) ∨ (¬ p2230) ∨ (¬ p5190) ∨ (¬ p3549) ∨ (¬ p4420) ∨ (¬ p4902) ∨ (¬ p2299) ∨ (¬ p3367) ∨ (¬ p4667) ∨ (¬ p4733))
    : p3093 ∨ (¬ p2982) ∨ (¬ p2850) ∨ (¬ p2459) ∨ (¬ p4733) ∨ p2177 ∨ (¬ p3367) ∨ (¬ p2230) ∨ (¬ p4335) ∨ (¬ p4355) ∨ (¬ p4420) ∨ p3146 ∨ (¬ p4902) ∨ (¬ p5190) ∨ p3309 ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4335 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))))));
    let u16 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u17 : p4667 := (Or.elim h73698 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u18 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u19 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    let u20 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u14 r0))));
    (Or.elim h69260 (fun q0 => (False.elim (q0 u16))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u15))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u19))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u13))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u20))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u10))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u12))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u18))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u6))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u17))) (fun r14 => (False.elim (r14 u4)))))))))))))))))))))))))))))))))

theorem step103418 (p2230 p2406 p2505 p2553 p2588 p2589 p3238 p3309 p4717 p5191 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73374 : p3238 ∨ p2406)
    (h73284 : p2589 ∨ p2230)
    (h69208 : (¬ p3309) ∨ (¬ p2505) ∨ (¬ p2588) ∨ (¬ p5191) ∨ (¬ p2589) ∨ (¬ p3238) ∨ (¬ p4717))
    : (¬ p3309) ∨ p2553 ∨ (¬ p5191) ∨ p2406 ∨ (¬ p2505) ∨ p2230 ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h69208 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step103431 (p2210 p2241 p2244 p2651 p2657 p2749 p4704 p4877 : Prop)
    (h73224 : p2244 ∨ p2241)
    (h73046 : p4704)
    (h73288 : p2657 ∨ p2651)
    (h68417 : (¬ p2210) ∨ (¬ p2657) ∨ (¬ p2244) ∨ (¬ p4877) ∨ (¬ p4704) ∨ (¬ p2749))
    : p2241 ∨ (¬ p4877) ∨ p2651 ∨ (¬ p2749) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2244 := (Or.elim h73224 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4704 := h73046;
    let u7 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h68417 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step103432 (p2210 p2241 p2244 p2284 p2630 p2737 p2747 p2810 p4117 p4704 p4877 : Prop)
    (h73224 : p2244 ∨ p2241)
    (h73316 : p2810 ∨ p2630)
    (h73046 : p4704)
    (h73302 : p2747 ∨ (¬ p2737))
    (h69087 : (¬ p2244) ∨ (¬ p2284) ∨ (¬ p4704) ∨ (¬ p2810) ∨ (¬ p4877) ∨ (¬ p2210) ∨ (¬ p4117) ∨ (¬ p2747))
    : (¬ p4877) ∨ p2241 ∨ p2630 ∨ (¬ p2284) ∨ (¬ p2737) ∨ (¬ p2210) ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4877 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2244 := (Or.elim h73224 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p4704 := h73046;
    let u10 : p2747 := (Or.elim h73302 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    (Or.elim h69087 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u10)))))))))))))))))

theorem step103438 (p2088 p2608 p3073 p3954 p5000 p5317 : Prop)
    (h73868 : p5000 ∨ p3073)
    (h73498 : p3954 ∨ p2608)
    (h68592 : (¬ p5000) ∨ (¬ p5317) ∨ (¬ p2088) ∨ (¬ p3954))
    : p3073 ∨ p2608 ∨ (¬ p2088) ∨ (¬ p5317) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5317 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5000 := (Or.elim h73868 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h68592 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step103443 (p2274 p2284 p2406 p3097 p3238 p3309 p3660 p3952 p4203 p4702 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73374 : p3238 ∨ p2406)
    (h73352 : p3097 ∨ p2274)
    (h69276 : (¬ p3952) ∨ (¬ p3238) ∨ (¬ p3309) ∨ (¬ p4702) ∨ (¬ p3660) ∨ (¬ p4203) ∨ (¬ p3097))
    : (¬ p3309) ∨ p2284 ∨ p2406 ∨ (¬ p3660) ∨ (¬ p4702) ∨ p2274 ∨ (¬ p4203) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h69276 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u9)))))))))))))))

theorem step103444 (p2177 p2274 p2284 p2299 p2406 p3097 p3238 p3379 p3452 p3660 p3952 p4203 p4702 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73496 : p3952 ∨ p2284)
    (h73352 : p3097 ∨ p2274)
    (h73374 : p3238 ∨ p2406)
    (h73234 : p2299 ∨ p2177)
    (h69295 : (¬ p3952) ∨ (¬ p3452) ∨ (¬ p3238) ∨ (¬ p4702) ∨ (¬ p2299) ∨ (¬ p3660) ∨ (¬ p4203) ∨ (¬ p3097))
    : p3379 ∨ p2284 ∨ p2274 ∨ (¬ p4702) ∨ p2406 ∨ (¬ p3660) ∨ (¬ p4203) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h69295 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u10)))))))))))))))))

theorem step103452 (p2156 p2192 p2284 p2797 p4195 p4790 p4960 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h68659 : p2284 ∨ (¬ p4960) ∨ (¬ p2192) ∨ (¬ p2156) ∨ (¬ p4195) ∨ (¬ p4790))
    : p2797 ∨ p2284 ∨ (¬ p4790) ∨ (¬ p2156) ∨ (¬ p2192) ∨ (¬ p4960) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h68659 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step103453 (p2241 p2247 p2249 p2274 p2440 p2553 p2588 p2590 p2630 p2751 p3422 p4703 p4748 p4790 p5219 : Prop)
    (h73964 : p5219 ∨ p3422)
    (h73714 : p4703 ∨ p2440)
    (h73740 : p4748 ∨ p2630)
    (h73226 : p2247 ∨ p2241)
    (h73282 : p2588 ∨ p2553)
    (h68443 : (¬ p5219) ∨ (¬ p2588) ∨ (¬ p2249) ∨ (¬ p2247) ∨ (¬ p4748) ∨ (¬ p4703) ∨ (¬ p4790) ∨ (¬ p2590) ∨ (¬ p2274) ∨ (¬ p2751))
    : (¬ p2274) ∨ (¬ p2249) ∨ (¬ p4790) ∨ p3422 ∨ p2440 ∨ p2630 ∨ (¬ p2590) ∨ (¬ p2751) ∨ p2241 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p5219 := (Or.elim h73964 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p4703 := (Or.elim h73714 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p4748 := (Or.elim h73740 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u14 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h68443 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u13))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step103463 (p2284 p2737 p2829 p2860 p3688 p3758 p4906 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73456 : p3758 ∨ p2860)
    (h68532 : (¬ p3758) ∨ (¬ p3688) ∨ (¬ p4906) ∨ (¬ p2284) ∨ (¬ p2737))
    : (¬ p2284) ∨ p2829 ∨ p2860 ∨ (¬ p2737) ∨ (¬ p4906) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h68532 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step103464 (p2440 p2663 p2685 p2850 p3363 p3475 p3572 p4650 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h69031 : (¬ p2850) ∨ (¬ p3572) ∨ (¬ p3475) ∨ (¬ p3363) ∨ (¬ p2663) ∨ (¬ p2440) ∨ (¬ p4650))
    : p2685 ∨ (¬ p2850) ∨ (¬ p4650) ∨ (¬ p2440) ∨ (¬ p3475) ∨ (¬ p2663) ∨ (¬ p3363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2685) := (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h69031 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step103466 (p2098 p2104 p2187 p2598 p2753 p2850 p4508 p4715 p4883 : Prop)
    (h73204 : p2104 ∨ p2098)
    (h73808 : p4883 ∨ (¬ p2850))
    (h73608 : p4508 ∨ (¬ p2187))
    (h68775 : (¬ p4883) ∨ (¬ p4508) ∨ (¬ p2598) ∨ (¬ p4715) ∨ (¬ p2104) ∨ (¬ p2753))
    : p2098 ∨ (¬ p2850) ∨ (¬ p2753) ∨ (¬ p2187) ∨ (¬ p4715) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4883 := (Or.elim h73808 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u8 : p4508 := (Or.elim h73608 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h68775 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step103471 (p2274 p2440 p2542 p2850 p3363 p3422 p3684 p4203 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73442 : p3684 ∨ p2850)
    (h68676 : (¬ p3422) ∨ (¬ p3363) ∨ (¬ p3684) ∨ (¬ p2542) ∨ (¬ p4203) ∨ (¬ p2274))
    : (¬ p3422) ∨ (¬ p2274) ∨ p2440 ∨ (¬ p3363) ∨ p2850 ∨ (¬ p4203) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3422 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h68676 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step103475 (p2230 p2406 p2608 p3238 p3954 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h73498 : p3954 ∨ p2608)
    (h72550 : (¬ p2230) ∨ (¬ p3238) ∨ (¬ p3954))
    : p2406 ∨ p2608 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2406) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h72550 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u4)))))))

theorem step103484 (p2274 p2417 p3097 p3125 p3744 p4276 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73453 : (¬ p3125) ∨ (¬ p3744))
    (h73352 : p3097 ∨ p2274)
    (h69057 : p3744 ∨ (¬ p4278) ∨ (¬ p4276) ∨ (¬ p3097))
    : p2417 ∨ (¬ p3125) ∨ p2274 ∨ (¬ p4276) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : (¬ p3744) := (Or.elim h73453 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h69057 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step103486 (p2630 p2727 p3016 p3136 p3879 p4315 p4717 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h69285 : (¬ p3016) ∨ (¬ p4315) ∨ (¬ p3879) ∨ (¬ p2727) ∨ (¬ p2630) ∨ (¬ p4717))
    : p3136 ∨ (¬ p3016) ∨ (¬ p2630) ∨ (¬ p3879) ∨ (¬ p4717) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h69285 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step103488 (p2241 p2608 p2737 p2747 p2774 p2780 p4732 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73302 : p2747 ∨ (¬ p2737))
    (h73732 : p4732 ∨ p2608)
    (h68705 : (¬ p2780) ∨ (¬ p2241) ∨ (¬ p2747) ∨ (¬ p4732))
    : p2774 ∨ (¬ p2737) ∨ p2608 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2747 := (Or.elim h73302 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u6 : p4732 := (Or.elim h73732 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h68705 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step103489 (p2241 p2563 p2573 p2579 p2750 p2881 p3379 p3541 p3570 p4558 p4714 p5189 : Prop)
    (h73948 : p5189 ∨ p3379)
    (h73418 : p3570 ∨ p2881)
    (h73720 : p4714 ∨ p2563)
    (h73274 : p2579 ∨ p2573)
    (h68344 : (¬ p5189) ∨ (¬ p3570) ∨ (¬ p2579) ∨ (¬ p3541) ∨ (¬ p2241) ∨ (¬ p4714) ∨ (¬ p4558) ∨ (¬ p2750))
    : (¬ p2241) ∨ (¬ p3541) ∨ p3379 ∨ (¬ p2750) ∨ p2881 ∨ (¬ p4558) ∨ p2563 ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p5189 := (Or.elim h73948 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4714 := (Or.elim h73720 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h68344 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step103493 (p2352 p2363 p3016 p3093 p3379 p3591 p4811 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h68334 : (¬ p3379) ∨ (¬ p3591) ∨ (¬ p2352) ∨ (¬ p3016) ∨ (¬ p4811) ∨ (¬ p2363))
    : p3093 ∨ (¬ p2352) ∨ (¬ p3016) ∨ (¬ p4811) ∨ (¬ p3379) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h68334 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step103494 (p2122 p2553 p3016 p3822 p4750 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h68291 : (¬ p2553) ∨ (¬ p3016) ∨ (¬ p4750) ∨ (¬ p3822))
    : (¬ p2553) ∨ p2122 ∨ (¬ p4750) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h68291 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step103498 (p2598 p2753 p2774 p2780 p2850 p4715 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h68713 : (¬ p2598) ∨ (¬ p2850) ∨ (¬ p2780) ∨ (¬ p4715) ∨ (¬ p2753))
    : (¬ p2598) ∨ p2774 ∨ (¬ p4715) ∨ (¬ p2850) ∨ (¬ p2753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h68713 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step103500 (p2528 p2850 p3609 p4340 p4608 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h68560 : (¬ p2528) ∨ (¬ p2850) ∨ (¬ p4608) ∨ (¬ p4340))
    : (¬ p2850) ∨ p3609 ∨ (¬ p2528) ∨ (¬ p4608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h68560 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step103502 (p2187 p2249 p2274 p2307 p2313 p2641 p2946 p3989 p4153 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73502 : p3989 ∨ p2187)
    (h68427 : p2946 ∨ (¬ p2313) ∨ (¬ p3989) ∨ (¬ p2641) ∨ (¬ p4153) ∨ (¬ p2249) ∨ (¬ p2274))
    : p2307 ∨ (¬ p2641) ∨ p2187 ∨ (¬ p2274) ∨ p2946 ∨ (¬ p4153) ∨ (¬ p2249) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2307) := (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h68427 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step103503 (p2363 p2528 p2534 p2553 p4602 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73662 : p4602 ∨ (¬ p2363))
    (h72563 : (¬ p4602) ∨ (¬ p2534) ∨ (¬ p2553))
    : (¬ p2553) ∨ p2528 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : p4602 := (Or.elim h73662 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h72563 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u0)))))))

theorem step103509 (p3136 p3256 p3609 p4121 p4704 : Prop)
    (h73046 : p4704)
    (h68588 : (¬ p3256) ∨ (¬ p4121) ∨ p3609 ∨ (¬ p3136) ∨ (¬ p4704))
    : (¬ p4121) ∨ p3609 ∨ (¬ p3256) ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4121 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4704 := h73046;
    (Or.elim h68588 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step103511 (p2088 p2098 p2104 p2122 p2363 p3609 p4340 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h73203 : (¬ p2098) ∨ (¬ p2104))
    (h72567 : (¬ p4340) ∨ p2104 ∨ (¬ p2088) ∨ (¬ p2122) ∨ (¬ p2363))
    : p3609 ∨ (¬ p2122) ∨ (¬ p2088) ∨ (¬ p2098) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : (¬ p2104) := (Or.elim h73203 (fun q0 => (False.elim (q0 u3))) (fun r0 => r0));
    (Or.elim h72567 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step103514 (p2274 p3097 p3125 p3286 p3292 p3323 p4153 p5273 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h73984 : p5273 ∨ p3323)
    (h73352 : p3097 ∨ p2274)
    (h68959 : (¬ p3125) ∨ (¬ p3292) ∨ (¬ p4153) ∨ (¬ p5273) ∨ (¬ p3097))
    : p3286 ∨ p3323 ∨ (¬ p4153) ∨ (¬ p3125) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3286) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p5273 := (Or.elim h73984 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h68959 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step103531 (p2088 p2166 p2210 p2608 p3954 p4495 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73600 : p4495 ∨ (¬ p2166))
    (h69089 : (¬ p4495) ∨ (¬ p2210) ∨ (¬ p2088) ∨ (¬ p3954))
    : p2608 ∨ (¬ p2088) ∨ (¬ p2210) ∨ (¬ p2166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4495 := (Or.elim h73600 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    (Or.elim h69089 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step103535 (p2210 p2274 p3093 p3399 p3591 p3923 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h72580 : (¬ p3923) ∨ (¬ p3399) ∨ (¬ p2274) ∨ (¬ p2210) ∨ (¬ p3591))
    : p3093 ∨ (¬ p2274) ∨ (¬ p3923) ∨ (¬ p2210) ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h72580 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step103536 (p2210 p2406 p3083 p3449 p3860 p4607 p4627 p4811 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h73676 : p4627 ∨ p2406)
    (h68901 : (¬ p4627) ∨ (¬ p3860) ∨ (¬ p3083) ∨ (¬ p4607) ∨ (¬ p4811) ∨ (¬ p2210))
    : p3449 ∨ (¬ p2210) ∨ p2406 ∨ (¬ p4607) ∨ (¬ p3083) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3449) := (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4607 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4627 := (Or.elim h73676 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h68901 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step103537 (p2210 p3201 p3379 p3399 p3452 p3876 p4210 p4644 p5217 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73394 : p3452 ∨ p3379)
    (h68340 : (¬ p3452) ∨ (¬ p3399) ∨ (¬ p4644) ∨ (¬ p4210) ∨ (¬ p3876) ∨ (¬ p2210) ∨ (¬ p5217))
    : (¬ p3399) ∨ p3201 ∨ (¬ p2210) ∨ (¬ p5217) ∨ p3379 ∨ (¬ p4644) ∨ (¬ p4210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5217 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h68340 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step103553 (p2098 p2104 p2187 p2774 p4889 : Prop)
    (h73204 : p2104 ∨ p2098)
    (h68704 : (¬ p2774) ∨ (¬ p4889) ∨ (¬ p2187) ∨ (¬ p2104))
    : p2098 ∨ (¬ p2774) ∨ (¬ p2187) ∨ (¬ p4889) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4889 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h68704 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step103556 (p2406 p2528 p3073 p3238 p4610 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h69219 : p2528 ∨ (¬ p3073) ∨ (¬ p4610) ∨ (¬ p3238))
    : (¬ p3073) ∨ p2528 ∨ p2406 ∨ (¬ p4610) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4610 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h69219 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step103558 (p2230 p2406 p2553 p2589 p3238 p3309 p4717 p5191 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h73284 : p2589 ∨ p2230)
    (h69221 : p2553 ∨ (¬ p3309) ∨ (¬ p5191) ∨ (¬ p2589) ∨ (¬ p3238) ∨ (¬ p4717))
    : (¬ p3309) ∨ p2553 ∨ (¬ p4717) ∨ p2406 ∨ p2230 ∨ (¬ p5191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h69221 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step103559 (p2241 p2247 p2727 p3083 p3193 p3276 p4256 p4425 p4809 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73226 : p2247 ∨ p2241)
    (h73542 : p4256 ∨ p3083)
    (h73770 : p4809 ∨ p2727)
    (h68639 : (¬ p4809) ∨ (¬ p3193) ∨ (¬ p4425) ∨ (¬ p4256) ∨ (¬ p2247))
    : p3276 ∨ p2241 ∨ (¬ p3193) ∨ p3083 ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p4809 := (Or.elim h73770 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h68639 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step103567 (p2177 p2341 p2696 p3425 p3551 p4778 p5256 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73980 : p5256 ∨ (¬ p3425))
    (h69000 : (¬ p5256) ∨ (¬ p4778) ∨ (¬ p3551) ∨ (¬ p2177) ∨ (¬ p2696))
    : p2341 ∨ (¬ p3425) ∨ (¬ p2177) ∨ (¬ p4778) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p5256 := (Or.elim h73980 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h69000 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step103571 (p2177 p2220 p2427 p2563 p2911 p3370 p3644 p4120 p4555 p4632 p4643 : Prop)
    (h73521 : (¬ p2220) ∨ (¬ p4120))
    (h73684 : p4643 ∨ p2427)
    (h73434 : p3644 ∨ p2911)
    (h69327 : (¬ p4643) ∨ (¬ p3644) ∨ p4120 ∨ (¬ p4632) ∨ (¬ p2177) ∨ (¬ p3370) ∨ (¬ p2563) ∨ (¬ p4555))
    : (¬ p3370) ∨ (¬ p2220) ∨ (¬ p4632) ∨ p2427 ∨ (¬ p4555) ∨ (¬ p2177) ∨ p2911 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3370 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p4120) := (Or.elim h73521 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u9 : p4643 := (Or.elim h73684 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h69327 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step103572 (p2406 p3238 p3379 p3399 p3452 p4366 p4646 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73569 : (¬ p3399) ∨ (¬ p4366))
    (h73374 : p3238 ∨ p2406)
    (h68629 : (¬ p3452) ∨ (¬ p3399) ∨ p4366 ∨ (¬ p3238) ∨ (¬ p4646))
    : (¬ p3399) ∨ p3379 ∨ (¬ p4646) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : (¬ p4366) := (Or.elim h73569 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h68629 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step103575 (p2528 p2563 p3146 p3692 p4110 p4509 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73516 : p4110 ∨ p2563)
    (h71236 : (¬ p3692) ∨ (¬ p4509) ∨ (¬ p2528) ∨ (¬ p4110))
    : (¬ p2528) ∨ p3146 ∨ (¬ p4509) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71236 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step103577 (p2132 p2138 p2156 p2528 p2563 p2651 p2655 p2657 p2659 p2685 p2696 p2737 p2747 p2901 p3051 p3572 p3646 p4558 p4714 p4785 p5190 : Prop)
    (h73720 : p4714 ∨ p2563)
    (h73420 : p3572 ∨ p2685)
    (h73288 : p2657 ∨ p2651)
    (h73436 : p3646 ∨ p2156)
    (h73302 : p2747 ∨ (¬ p2737))
    (h73758 : p4785 ∨ p2696)
    (h73214 : p2138 ∨ p2132)
    (h71237 : (¬ p4785) ∨ (¬ p2747) ∨ (¬ p2659) ∨ (¬ p2657) ∨ (¬ p2655) ∨ (¬ p2528) ∨ (¬ p3646) ∨ (¬ p4558) ∨ (¬ p5190) ∨ (¬ p4714) ∨ (¬ p2138) ∨ (¬ p2901) ∨ (¬ p3051) ∨ (¬ p3572))
    : (¬ p3051) ∨ (¬ p4558) ∨ p2563 ∨ p2685 ∨ (¬ p2655) ∨ p2651 ∨ (¬ p2528) ∨ p2156 ∨ (¬ p2659) ∨ (¬ p2737) ∨ p2696 ∨ (¬ p2901) ∨ p2132 ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))));
    let u14 : p4714 := (Or.elim h73720 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u15 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u16 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u17 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u18 : p2747 := (Or.elim h73302 (fun q0 => q0) (fun r0 => (False.elim (r0 u9))));
    let u19 : p4785 := (Or.elim h73758 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    let u20 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u12 r0))));
    (Or.elim h71237 (fun q0 => (False.elim (q0 u19))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u18))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u16))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u17))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u13))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u14))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u20))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u11))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u0))) (fun r12 => (False.elim (r12 u15)))))))))))))))))))))))))))))

theorem step103582 (p2190 p2363 p2528 p3146 p3323 p4037 p4384 p4564 p4600 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73660 : p4600 ∨ p2363)
    (h71021 : (¬ p4600) ∨ (¬ p4037) ∨ (¬ p2528) ∨ (¬ p3146) ∨ (¬ p4564) ∨ (¬ p2190) ∨ (¬ p4384))
    : p3323 ∨ (¬ p2528) ∨ (¬ p3146) ∨ (¬ p4384) ∨ (¬ p2190) ∨ p2363 ∨ (¬ p4564) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4384 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p4600 := (Or.elim h73660 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h71021 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step103584 (p2274 p2295 p2901 p3568 p4320 p4557 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73636 : p4557 ∨ (¬ p2274))
    (h73551 : (¬ p2901) ∨ (¬ p4320))
    (h71162 : (¬ p4557) ∨ p4320 ∨ (¬ p3568))
    : p2295 ∨ (¬ p2274) ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2295) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u5 : (¬ p4320) := (Or.elim h73551 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h71162 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step103586 (p2088 p2177 p2230 p2264 p2274 p2331 p2341 p2363 p2437 p2459 p2641 p2651 p2656 p2657 p2727 p2911 p2996 p3031 p3097 p3323 p3389 p3422 p3434 p3584 p4037 p4204 p4502 p4555 p4556 p4602 p4667 p4809 p4975 p4992 p5201 p5214 : Prop)
    (h73604 : p4502 ∨ (¬ p2177))
    (h73662 : p4602 ∨ (¬ p2363))
    (h73425 : (¬ p3422) ∨ (¬ p3584))
    (h73352 : p3097 ∨ p2274)
    (h73698 : p4667 ∨ (¬ p2459))
    (h73770 : p4809 ∨ p2727)
    (h73508 : p4037 ∨ p3323)
    (h73288 : p2657 ∨ p2651)
    (h70030 : (¬ p2641) ∨ (¬ p3434) ∨ p3584 ∨ (¬ p4667) ∨ (¬ p4556) ∨ (¬ p4555) ∨ (¬ p3097) ∨ (¬ p4204) ∨ (¬ p2230) ∨ (¬ p4992) ∨ (¬ p5214) ∨ (¬ p2996) ∨ (¬ p3031) ∨ (¬ p4809) ∨ (¬ p4037) ∨ (¬ p2911) ∨ (¬ p2341) ∨ (¬ p2264) ∨ (¬ p3389) ∨ (¬ p5201) ∨ (¬ p2437) ∨ (¬ p2088) ∨ (¬ p4975) ∨ (¬ p2657) ∨ (¬ p2656) ∨ (¬ p4602) ∨ (¬ p2331) ∨ (¬ p4502))
    : (¬ p2088) ∨ (¬ p3434) ∨ (¬ p2656) ∨ (¬ p4556) ∨ (¬ p2177) ∨ (¬ p4555) ∨ (¬ p2363) ∨ (¬ p3422) ∨ (¬ p4204) ∨ p2274 ∨ (¬ p5214) ∨ (¬ p3389) ∨ (¬ p2459) ∨ (¬ p2641) ∨ (¬ p2230) ∨ p2727 ∨ p3323 ∨ (¬ p4992) ∨ (¬ p3031) ∨ (¬ p2264) ∨ (¬ p2341) ∨ (¬ p2996) ∨ (¬ p4975) ∨ (¬ p2437) ∨ (¬ p5201) ∨ p2651 ∨ (¬ p2911) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5214 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))));
    let u14 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))));
    let u15 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))));
    let u16 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))));
    let u17 : p4992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))));
    let u18 : p3031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))));
    let u19 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))));
    let u20 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))));
    let u21 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))));
    let u22 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))));
    let u23 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))));
    let u24 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))));
    let u25 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))));
    let u26 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))));
    let u27 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))))))))))))))))));
    let u28 : p4502 := (Or.elim h73604 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u29 : p4602 := (Or.elim h73662 (fun q0 => q0) (fun r0 => (False.elim (r0 u6))));
    let u30 : (¬ p3584) := (Or.elim h73425 (fun q0 => (False.elim (q0 u7))) (fun r0 => r0));
    let u31 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u32 : p4667 := (Or.elim h73698 (fun q0 => q0) (fun r0 => (False.elim (r0 u12))));
    let u33 : p4809 := (Or.elim h73770 (fun q0 => q0) (fun r0 => (False.elim (u15 r0))));
    let u34 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u16 r0))));
    let u35 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u25 r0))));
    (Or.elim h70030 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u30 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u32))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u31))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u14))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u17))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u10))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u21))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u18))) (fun r12 => (Or.elim r12 (fun q13 => (False.elim (q13 u33))) (fun r13 => (Or.elim r13 (fun q14 => (False.elim (q14 u34))) (fun r14 => (Or.elim r14 (fun q15 => (False.elim (q15 u26))) (fun r15 => (Or.elim r15 (fun q16 => (False.elim (q16 u20))) (fun r16 => (Or.elim r16 (fun q17 => (False.elim (q17 u19))) (fun r17 => (Or.elim r17 (fun q18 => (False.elim (q18 u11))) (fun r18 => (Or.elim r18 (fun q19 => (False.elim (q19 u24))) (fun r19 => (Or.elim r19 (fun q20 => (False.elim (q20 u23))) (fun r20 => (Or.elim r20 (fun q21 => (False.elim (q21 u0))) (fun r21 => (Or.elim r21 (fun q22 => (False.elim (q22 u22))) (fun r22 => (Or.elim r22 (fun q23 => (False.elim (q23 u35))) (fun r23 => (Or.elim r23 (fun q24 => (False.elim (q24 u2))) (fun r24 => (Or.elim r24 (fun q25 => (False.elim (q25 u29))) (fun r25 => (Or.elim r25 (fun q26 => (False.elim (q26 u27))) (fun r26 => (False.elim (r26 u28)))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end ElevenRUP
