import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step94246 (p2470 p2663 p2761 p3083 p3343 p3425 p3670 p4256 p4638 p4786 p5228 p5387 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h73542 : p4256 ∨ p3083)
    (h61404 : (¬ p2470) ∨ (¬ p2663) ∨ (¬ p2761) ∨ (¬ p3343) ∨ (¬ p3425) ∨ (¬ p4256) ∨ (¬ p4638) ∨ (¬ p4786) ∨ (¬ p5228) ∨ (¬ p5387))
    : p3670 ∨ (¬ p3343) ∨ (¬ p4786) ∨ (¬ p4638) ∨ (¬ p5228) ∨ (¬ p3425) ∨ (¬ p2761) ∨ (¬ p2663) ∨ p3083 ∨ (¬ p2470) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4638 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5228 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h61404 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (r8 u10)))))))))))))))))))))

theorem step94247 (p2459 p3266 p3670 p4802 p5338 p5387 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h41309 : (¬ p2459) ∨ (¬ p3266) ∨ (¬ p4802) ∨ (¬ p5338) ∨ (¬ p5387))
    : p3670 ∨ (¬ p5338) ∨ (¬ p3266) ∨ (¬ p2459) ∨ (¬ p4802) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : p5338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4802 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41309 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step94248 (p2449 p2696 p2742 p2996 p3027 p3276 p3367 p3585 p3670 p4641 p5158 p5387 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h73340 : p3027 ∨ p2996)
    (h73428 : p3585 ∨ p3367)
    (h72049 : (¬ p5387) ∨ (¬ p3585) ∨ (¬ p4641) ∨ (¬ p5158) ∨ (¬ p2742) ∨ (¬ p3276) ∨ (¬ p2449) ∨ (¬ p2696) ∨ (¬ p3027))
    : p3670 ∨ (¬ p3276) ∨ (¬ p2742) ∨ p2996 ∨ (¬ p4641) ∨ (¬ p5158) ∨ (¬ p2449) ∨ (¬ p2696) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5158 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h72049 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u10)))))))))))))))))))

theorem step94249 (p2685 p3286 p3506 p3670 p5387 p5453 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h46481 : (¬ p2685) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p5387) ∨ (¬ p5453))
    : p3670 ∨ (¬ p3506) ∨ (¬ p3286) ∨ (¬ p5453) ∨ (¬ p2685) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5453 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h46481 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step94252 (p2246 p2744 p2761 p2946 p3146 p3156 p3366 p3425 p3670 p4669 p5228 p5387 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h41195 : (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2761) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p4669) ∨ (¬ p5228) ∨ (¬ p5387))
    : (¬ p2246) ∨ p3670 ∨ (¬ p5228) ∨ (¬ p2761) ∨ (¬ p2744) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p2946) ∨ (¬ p4669) ∨ (¬ p3366) ∨ (¬ p3425) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3670) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5228 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41195 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (False.elim (r9 u11)))))))))))))))))))))))

theorem step94253 (p2707 p2737 p2761 p3588 p3670 p5228 p5387 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h73430 : p3588 ∨ p2707)
    (h63623 : (¬ p2737) ∨ (¬ p2761) ∨ (¬ p3588) ∨ (¬ p5228) ∨ (¬ p5387))
    : p3670 ∨ (¬ p2761) ∨ (¬ p5228) ∨ p2707 ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5228 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3588 := (Or.elim h73430 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63623 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step94254 (p2753 p2774 p3266 p3599 p3670 p4379 p5387 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h73572 : p4379 ∨ p3599)
    (h61640 : (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3266) ∨ (¬ p4379) ∨ (¬ p5387))
    : p3670 ∨ p3599 ∨ (¬ p2753) ∨ (¬ p3266) ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3599) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4379 := (Or.elim h73572 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h61640 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step94255 (p2608 p2707 p2761 p3588 p3670 p3954 p5228 p5387 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h73498 : p3954 ∨ p2608)
    (h73430 : p3588 ∨ p2707)
    (h43912 : (¬ p2761) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p5228) ∨ (¬ p5387))
    : p3670 ∨ p2608 ∨ p2707 ∨ (¬ p5228) ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5228 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3588 := (Or.elim h73430 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43912 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step94259 (p2144 p2651 p2657 p3016 p3212 p3564 p3574 p3670 p3680 p4137 p4789 p5267 p5387 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h73288 : p2657 ∨ p2651)
    (h73524 : p4137 ∨ p3564)
    (h73422 : p3574 ∨ p3016)
    (h64563 : (¬ p2144) ∨ (¬ p2657) ∨ (¬ p3212) ∨ (¬ p3574) ∨ (¬ p3680) ∨ (¬ p4137) ∨ (¬ p4789) ∨ (¬ p5267) ∨ (¬ p5387))
    : p3670 ∨ (¬ p3212) ∨ (¬ p5267) ∨ (¬ p4789) ∨ (¬ p2144) ∨ (¬ p3680) ∨ p2651 ∨ p3564 ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5267 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h64563 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step94262 (p3276 p3670 p4425 p5164 p5387 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h73577 : (¬ p3276) ∨ (¬ p4425))
    (h32947 : p4425 ∨ (¬ p5164) ∨ (¬ p5387))
    : p3670 ∨ (¬ p5164) ∨ (¬ p3276) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : p5164 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p4425) := (Or.elim h73577 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h32947 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step94263 (p2295 p2331 p2396 p3346 p3670 p3680 p3905 p3951 p4786 p5164 p5387 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h63480 : (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2396) ∨ (¬ p3346) ∨ (¬ p3680) ∨ (¬ p3905) ∨ (¬ p3951) ∨ (¬ p4786) ∨ (¬ p5164) ∨ (¬ p5387))
    : p3670 ∨ (¬ p5164) ∨ (¬ p4786) ∨ (¬ p3905) ∨ (¬ p3680) ∨ (¬ p3346) ∨ (¬ p2295) ∨ (¬ p2396) ∨ (¬ p2331) ∨ (¬ p3951) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : p5164 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h63480 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (False.elim (r8 u10)))))))))))))))))))))

theorem step94276 (p3506 p3670 p5387 p5458 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h20893 : (¬ p3506) ∨ (¬ p5387) ∨ (¬ p5458))
    : p3670 ∨ (¬ p3506) ∨ (¬ p5458) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5458 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h20893 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step94283 (p2230 p2427 p2608 p3519 p3670 p3830 p3834 p4029 p4129 p4376 p4826 p5387 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h73474 : p3834 ∨ p3830)
    (h53524 : (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p3834) ∨ (¬ p4029) ∨ (¬ p4129) ∨ (¬ p4376) ∨ (¬ p4826) ∨ (¬ p5387))
    : (¬ p4129) ∨ p3670 ∨ (¬ p4826) ∨ (¬ p3519) ∨ (¬ p2427) ∨ (¬ p2608) ∨ p3830 ∨ (¬ p2230) ∨ (¬ p4376) ∨ (¬ p4029) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4129 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3670) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4029 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h53524 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (r8 u10)))))))))))))))))))))

theorem step94284 (p2098 p2104 p2284 p2946 p3125 p3266 p3670 p4330 p4786 p5338 p5387 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h73204 : p2104 ∨ p2098)
    (h49100 : (¬ p2104) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p3266) ∨ (¬ p4330) ∨ (¬ p4786) ∨ (¬ p5338) ∨ (¬ p5387))
    : p3670 ∨ (¬ p5338) ∨ p2098 ∨ (¬ p3125) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3266) ∨ (¬ p4786) ∨ (¬ p4330) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : p5338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h49100 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step94286 (p2737 p2743 p3670 p3707 p5333 p5387 p5460 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h73298 : p2743 ∨ p2737)
    (h41228 : (¬ p2743) ∨ (¬ p3707) ∨ (¬ p5333) ∨ (¬ p5387) ∨ (¬ p5460))
    : (¬ p5333) ∨ p3670 ∨ (¬ p3707) ∨ p2737 ∨ (¬ p5460) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3670) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5460 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41228 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step94287 (p2248 p2608 p2651 p3016 p3599 p3670 p3888 p3954 p4379 p5250 p5387 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h73572 : p4379 ∨ p3599)
    (h73498 : p3954 ∨ p2608)
    (h55611 : (¬ p2248) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3888) ∨ (¬ p3954) ∨ (¬ p4379) ∨ (¬ p5250) ∨ (¬ p5387))
    : (¬ p3888) ∨ p3670 ∨ (¬ p3016) ∨ (¬ p5250) ∨ (¬ p2248) ∨ p3599 ∨ p2608 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3888 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3670) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3599) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4379 := (Or.elim h73572 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h55611 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u8)))))))))))))))))

theorem step94290 (p2598 p3055 p3367 p3599 p3670 p3873 p4379 p5387 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h73572 : p4379 ∨ p3599)
    (h73350 : p3055 ∨ p2598)
    (h48480 : (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3873) ∨ (¬ p4379) ∨ (¬ p5387))
    : p3670 ∨ p3599 ∨ (¬ p3367) ∨ p2598 ∨ (¬ p3873) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3599) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4379 := (Or.elim h73572 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48480 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step94292 (p2248 p2437 p2608 p2651 p3599 p3670 p3868 p3954 p4379 p4826 p5387 : Prop)
    (h73572 : p4379 ∨ p3599)
    (h74026 : p5387 ∨ p3670)
    (h73498 : p3954 ∨ p2608)
    (h62533 : (¬ p2248) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p3868) ∨ (¬ p3954) ∨ (¬ p4379) ∨ (¬ p4826) ∨ (¬ p5387))
    : p3599 ∨ p3670 ∨ (¬ p4826) ∨ p2608 ∨ (¬ p2248) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p3868) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3599) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3670) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4379 := (Or.elim h73572 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62533 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u9)))))))))))))))))

theorem step94297 (p2352 p2573 p2608 p3599 p3670 p3954 p3979 p4379 p5119 p5190 p5387 : Prop)
    (h73572 : p4379 ∨ p3599)
    (h74026 : p5387 ∨ p3670)
    (h73498 : p3954 ∨ p2608)
    (h56169 : (¬ p2352) ∨ (¬ p2573) ∨ (¬ p3954) ∨ (¬ p3979) ∨ (¬ p4379) ∨ (¬ p5119) ∨ (¬ p5190) ∨ (¬ p5387))
    : p3599 ∨ p3670 ∨ (¬ p2352) ∨ (¬ p2573) ∨ p2608 ∨ (¬ p5190) ∨ (¬ p5119) ∨ (¬ p3979) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3599) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3670) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4379 := (Or.elim h73572 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56169 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u9)))))))))))))))))

theorem step94310 (p2608 p3830 p3834 p5333 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h39360 : (¬ p2608) ∨ (¬ p3834) ∨ (¬ p5333))
    : (¬ p5333) ∨ p3830 ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h39360 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u0)))))))

theorem step94316 (p2396 p3425 p3619 p4029 p4107 p4477 p5362 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h59840 : (¬ p3425) ∨ (¬ p3619) ∨ (¬ p4029) ∨ (¬ p4107) ∨ (¬ p4477) ∨ (¬ p5362))
    : (¬ p3619) ∨ (¬ p4029) ∨ (¬ p3425) ∨ p2396 ∨ (¬ p4477) ∨ (¬ p5362) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4029 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h59840 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step94324 (p2667 p2946 p2952 p3987 p4153 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h6289 : (¬ p2667) ∨ (¬ p2952) ∨ (¬ p3987) ∨ (¬ p4153))
    : (¬ p3987) ∨ (¬ p2667) ∨ (¬ p4153) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3987 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h6289 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step94325 (p2254 p2274 p2295 p2470 p2493 p2509 p2946 p2952 p3568 p3958 p4079 p4153 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73416 : p3568 ∨ p2295)
    (h62354 : (¬ p2254) ∨ (¬ p2274) ∨ (¬ p2470) ∨ (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2952) ∨ (¬ p3568) ∨ (¬ p3958) ∨ (¬ p4079) ∨ (¬ p4153))
    : (¬ p2509) ∨ (¬ p2470) ∨ (¬ p2274) ∨ (¬ p4153) ∨ (¬ p3958) ∨ (¬ p2254) ∨ p2946 ∨ p2295 ∨ (¬ p2493) ∨ (¬ p4079) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h62354 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step94332 (p2363 p2383 p2387 p2510 p2528 p2581 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73246 : p2387 ∨ p2383)
    (h48602 : (¬ p2387) ∨ (¬ p2510) ∨ (¬ p2528) ∨ (¬ p2581) ∨ (¬ p4347))
    : (¬ p2528) ∨ p2363 ∨ (¬ p2510) ∨ p2383 ∨ (¬ p2581) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2510 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48602 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step94335 (p2187 p2797 p3005 p3989 p4195 p4417 p4560 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h72955 : p4560)
    (h73502 : p3989 ∨ p2187)
    (h51538 : (¬ p3005) ∨ (¬ p3989) ∨ (¬ p4195) ∨ (¬ p4417) ∨ (¬ p4560))
    : p2797 ∨ (¬ p3005) ∨ (¬ p4417) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4560 := h72955;
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h51538 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step94337 (p2331 p2352 p2963 p3166 p3956 p4417 p4976 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73500 : p3956 ∨ p2352)
    (h41180 : (¬ p2963) ∨ (¬ p3166) ∨ (¬ p3956) ∨ (¬ p4417) ∨ (¬ p4976))
    : (¬ p4417) ∨ p2331 ∨ p2352 ∨ (¬ p4976) ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4976 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41180 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step94342 (p2417 p2449 p3096 p3156 p3920 p3947 p4386 p4509 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h64477 : (¬ p2417) ∨ (¬ p3096) ∨ (¬ p3156) ∨ (¬ p3920) ∨ (¬ p3947) ∨ (¬ p4386) ∨ (¬ p4509))
    : (¬ p2417) ∨ (¬ p3920) ∨ p2449 ∨ (¬ p4386) ∨ (¬ p4509) ∨ (¬ p3096) ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3920 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h64477 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step94344 (p2284 p2449 p3246 p3947 p4386 p4555 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h41263 : (¬ p2284) ∨ (¬ p3246) ∨ (¬ p3947) ∨ (¬ p4386) ∨ (¬ p4555))
    : (¬ p3246) ∨ p2449 ∨ (¬ p4555) ∨ (¬ p2284) ∨ (¬ p4386) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41263 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step94346 (p2264 p2284 p2341 p3553 p3691 p4386 p4555 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h63637 : (¬ p2284) ∨ (¬ p2341) ∨ (¬ p3553) ∨ (¬ p3691) ∨ (¬ p4386) ∨ (¬ p4555))
    : (¬ p2341) ∨ (¬ p3691) ∨ (¬ p4386) ∨ (¬ p2284) ∨ p2264 ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63637 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step94347 (p2264 p2341 p2573 p2579 p3553 p4241 p4386 p4715 p5201 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h73274 : p2579 ∨ p2573)
    (h50368 : (¬ p2341) ∨ (¬ p2579) ∨ (¬ p3553) ∨ (¬ p4241) ∨ (¬ p4386) ∨ (¬ p4715) ∨ (¬ p5201))
    : (¬ p2341) ∨ (¬ p4386) ∨ (¬ p4241) ∨ p2264 ∨ (¬ p5201) ∨ p2573 ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h50368 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step94351 (p2220 p2954 p2992 p3189 p3662 p4120 p4311 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h73440 : p3662 ∨ p2992)
    (h41568 : (¬ p2954) ∨ (¬ p3189) ∨ (¬ p3662) ∨ (¬ p4120) ∨ (¬ p4311))
    : (¬ p4311) ∨ (¬ p3189) ∨ (¬ p2954) ∨ p2220 ∨ p2992 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4311 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41568 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step94352 (p2373 p3693 p5839 : Prop)
    (h74129 : p2373 ∨ (¬ p5839))
    (h12029 : p3693 ∨ p5839)
    : p3693 ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3693) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5839) := (Or.elim h74129 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12029 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step94353 (p2373 p4607 p5839 : Prop)
    (h74129 : p2373 ∨ (¬ p5839))
    (h12031 : p4607 ∨ p5839)
    : p4607 ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4607) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5839) := (Or.elim h74129 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12031 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step94371 (p2911 p2996 p3644 p3842 p4349 p4378 p4653 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h56661 : (¬ p2996) ∨ (¬ p3644) ∨ (¬ p3842) ∨ (¬ p4349) ∨ (¬ p4378) ∨ (¬ p4653))
    : (¬ p3842) ∨ (¬ p2996) ∨ (¬ p4653) ∨ p2911 ∨ (¬ p4378) ∨ (¬ p4349) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3842 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4653 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4378 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4349 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56661 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step94376 (p2252 p3286 p3292 p3842 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h18477 : (¬ p2252) ∨ (¬ p3292) ∨ (¬ p3842))
    : p3286 ∨ (¬ p3842) ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3286) := (fun h => hn (Or.inl h));
    let u1 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h18477 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step94377 (p2992 p3662 p3842 p4314 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h38290 : (¬ p3662) ∨ (¬ p3842) ∨ (¬ p4314))
    : (¬ p3842) ∨ p2992 ∨ (¬ p4314) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3842 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4314 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h38290 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u2)))))))

theorem step94378 (p2241 p3266 p3506 p3842 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h44928 : (¬ p2241) ∨ (¬ p3506) ∨ (¬ p3842) ∨ (¬ p4444))
    : p3266 ∨ (¬ p3842) ∨ (¬ p2241) ∨ (¬ p3506) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h44928 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step94380 (p2406 p2440 p2542 p3238 p3402 p3842 p5177 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73374 : p3238 ∨ p2406)
    (h44841 : (¬ p2542) ∨ (¬ p3238) ∨ (¬ p3402) ∨ (¬ p3842) ∨ (¬ p5177))
    : (¬ p5177) ∨ (¬ p3402) ∨ p2440 ∨ p2406 ∨ (¬ p3842) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44841 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step94382 (p2241 p3461 p3506 p3842 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h47643 : (¬ p2241) ∨ (¬ p3506) ∨ (¬ p3842) ∨ (¬ p4191))
    : p3461 ∨ (¬ p3842) ∨ (¬ p2241) ∨ (¬ p3506) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h47643 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step94385 (p2727 p3842 p4111 p5170 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h20040 : (¬ p3842) ∨ (¬ p4111) ∨ (¬ p5170))
    : (¬ p3842) ∨ (¬ p5170) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3842 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20040 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step94388 (p2241 p2352 p2573 p2579 p3506 p3842 p3956 p5123 p5193 p5580 : Prop)
    (h73500 : p3956 ∨ p2352)
    (h73274 : p2579 ∨ p2573)
    (h50100 : (¬ p2241) ∨ (¬ p2579) ∨ (¬ p3506) ∨ (¬ p3842) ∨ (¬ p3956) ∨ (¬ p5123) ∨ (¬ p5193) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p5123) ∨ (¬ p2241) ∨ p2352 ∨ (¬ p5193) ∨ p2573 ∨ (¬ p3506) ∨ (¬ p3842) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h50100 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step94389 (p2241 p2911 p3389 p3506 p3540 p3644 p3842 p5123 p5193 p5558 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73402 : p3540 ∨ p3389)
    (h51430 : (¬ p2241) ∨ (¬ p3506) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p3842) ∨ (¬ p5123) ∨ (¬ p5193) ∨ (¬ p5558))
    : (¬ p5558) ∨ (¬ p3506) ∨ (¬ p2241) ∨ p2911 ∨ (¬ p3842) ∨ (¬ p5123) ∨ p3389 ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5558 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h51430 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step94391 (p2253 p2651 p2727 p3506 p3842 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h51680 : (¬ p2253) ∨ (¬ p2651) ∨ (¬ p3506) ∨ (¬ p3842) ∨ (¬ p4111))
    : (¬ p3506) ∨ p2727 ∨ (¬ p2253) ∨ (¬ p3842) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h51680 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step94393 (p2440 p2727 p3842 p4111 p4953 p5175 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h41651 : (¬ p2440) ∨ (¬ p3842) ∨ (¬ p4111) ∨ (¬ p4953) ∨ (¬ p5175))
    : p2727 ∨ (¬ p5175) ∨ (¬ p3842) ∨ (¬ p2440) ∨ (¬ p4953) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p5175 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41651 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step94402 (p2230 p2241 p2427 p2589 p3506 p3842 p4235 p4831 p5193 p5660 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h73536 : p4235 ∨ p2427)
    (h64086 : (¬ p2241) ∨ (¬ p2589) ∨ (¬ p3506) ∨ (¬ p3842) ∨ (¬ p4235) ∨ (¬ p4831) ∨ (¬ p5193) ∨ (¬ p5660))
    : (¬ p5660) ∨ (¬ p3506) ∨ p2230 ∨ (¬ p4831) ∨ p2427 ∨ (¬ p3842) ∨ (¬ p2241) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5660 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h64086 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step94403 (p2230 p2241 p2373 p2589 p3506 p3842 p3880 p5123 p5193 p5568 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h73490 : p3880 ∨ p2373)
    (h51409 : (¬ p2241) ∨ (¬ p2589) ∨ (¬ p3506) ∨ (¬ p3842) ∨ (¬ p3880) ∨ (¬ p5123) ∨ (¬ p5193) ∨ (¬ p5568))
    : (¬ p5568) ∨ (¬ p3506) ∨ p2230 ∨ (¬ p3842) ∨ p2373 ∨ (¬ p5123) ∨ (¬ p2241) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5568 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51409 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step94406 (p2241 p2553 p2573 p2579 p2588 p3506 p3842 p4260 p4831 p5193 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73282 : p2588 ∨ p2553)
    (h54490 : (¬ p2241) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3506) ∨ (¬ p3842) ∨ (¬ p4260) ∨ (¬ p4831) ∨ (¬ p5193))
    : (¬ p4260) ∨ (¬ p3506) ∨ p2573 ∨ (¬ p2241) ∨ (¬ p5193) ∨ p2553 ∨ (¬ p4831) ∨ (¬ p3842) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4260 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h54490 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step94409 (p2685 p3572 p3755 p4035 p4429 : Prop)
    (h73505 : (¬ p3755) ∨ (¬ p4035))
    (h73420 : p3572 ∨ p2685)
    (h19185 : (¬ p3572) ∨ p4035 ∨ (¬ p4429))
    : (¬ p4429) ∨ (¬ p3755) ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4429 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4035) := (Or.elim h73505 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u4 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h19185 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step94414 (p3845 p3848 p3851 : Prop)
    (h73475 : (¬ p3845) ∨ (¬ p3851))
    (h5688 : p3848 ∨ p3851)
    : p3848 ∨ (¬ p3845) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3848) := (fun h => hn (Or.inl h));
    let u1 : p3845 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3851) := (Or.elim h73475 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h5688 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step94417 (p2641 p3848 p4154 p5274 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h34989 : p3848 ∨ (¬ p4154) ∨ (¬ p5274))
    : p3848 ∨ p2641 ∨ (¬ p5274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3848) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h34989 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step94419 (p2807 p3246 p3286 p3292 p4280 p4656 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h41907 : (¬ p2807) ∨ (¬ p3246) ∨ (¬ p3292) ∨ (¬ p4280) ∨ (¬ p4656))
    : p3286 ∨ (¬ p4656) ∨ (¬ p4280) ∨ (¬ p3246) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3286) := (fun h => hn (Or.inl h));
    let u1 : p4656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4280 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41907 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step94421 (p2264 p2807 p3286 p3292 p4656 p4666 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h48484 : (¬ p2264) ∨ (¬ p2807) ∨ (¬ p3292) ∨ (¬ p4656) ∨ (¬ p4666))
    : (¬ p4656) ∨ p3286 ∨ (¬ p4666) ∨ (¬ p2807) ∨ (¬ p2264) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4656 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h48484 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step94425 (p2252 p2396 p2996 p3027 p3286 p3292 p4656 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h73340 : p3027 ∨ p2996)
    (h72052 : (¬ p2252) ∨ (¬ p2396) ∨ (¬ p4656) ∨ (¬ p3027) ∨ (¬ p3292))
    : p3286 ∨ (¬ p2396) ∨ (¬ p2252) ∨ p2996 ∨ (¬ p4656) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3286) := (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h72052 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step94426 (p2396 p2996 p3027 p3848 p4656 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h72053 : (¬ p3848) ∨ (¬ p4656) ∨ (¬ p2396) ∨ (¬ p3027))
    : (¬ p3848) ∨ (¬ p2396) ∨ (¬ p4656) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3848 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h72053 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step94427 (p2761 p3506 p4381 p4656 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h19867 : (¬ p3506) ∨ (¬ p4381) ∨ (¬ p4656))
    : (¬ p3506) ∨ p2761 ∨ (¬ p4656) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h19867 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step94428 (p2264 p2363 p2459 p3325 p3553 p4348 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h73562 : p4348 ∨ p2459)
    (h72054 : (¬ p3553) ∨ (¬ p4348) ∨ (¬ p3325) ∨ (¬ p2363))
    : p2264 ∨ (¬ p3325) ∨ p2459 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2264) := (fun h => hn (Or.inl h));
    let u1 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h72054 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step94429 (p2264 p2352 p2553 p2588 p3550 p3553 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h73282 : p2588 ∨ p2553)
    (h72055 : (¬ p2588) ∨ (¬ p2352) ∨ (¬ p3550) ∨ (¬ p3553))
    : (¬ p2352) ∨ (¬ p3550) ∨ p2264 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h72055 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step94434 (p3189 p3833 p3853 p4349 p4360 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h37522 : (¬ p3833) ∨ (¬ p3853) ∨ (¬ p4349) ∨ (¬ p4360))
    : (¬ p3833) ∨ (¬ p4349) ∨ (¬ p3853) ∨ p3189 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3833 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4349 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3853 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h37522 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step94440 (p2341 p2662 p2717 p2797 p3551 p4195 p4336 p4781 p5197 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73408 : p3551 ∨ p2341)
    (h69686 : (¬ p3551) ∨ (¬ p2717) ∨ (¬ p4195) ∨ (¬ p4336) ∨ (¬ p5197) ∨ (¬ p4781) ∨ (¬ p2662))
    : p2797 ∨ (¬ p2717) ∨ (¬ p2662) ∨ (¬ p4781) ∨ p2341 ∨ (¬ p4336) ∨ (¬ p5197) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h69686 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step94442 (p2449 p2630 p2810 p3434 p3947 p4652 p4781 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73316 : p2810 ∨ p2630)
    (h41701 : (¬ p2810) ∨ (¬ p3434) ∨ (¬ p3947) ∨ (¬ p4652) ∨ (¬ p4781))
    : (¬ p3434) ∨ p2449 ∨ (¬ p4781) ∨ p2630 ∨ (¬ p4652) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41701 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step94444 (p2264 p2717 p2807 p3414 p3553 p4781 : Prop)
    (h73392 : p3414 ∨ p2807)
    (h73410 : p3553 ∨ p2264)
    (h72059 : (¬ p2717) ∨ (¬ p3553) ∨ (¬ p4781) ∨ (¬ p3414))
    : (¬ p2717) ∨ p2807 ∨ (¬ p4781) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2807) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h72059 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step94445 (p2573 p2630 p2807 p2810 p3414 p3461 p3564 p4236 p4253 p4391 p4419 p4781 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73392 : p3414 ∨ p2807)
    (h46960 : (¬ p2573) ∨ (¬ p2810) ∨ (¬ p3414) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p4236) ∨ (¬ p4253) ∨ (¬ p4391) ∨ (¬ p4419) ∨ (¬ p4781))
    : (¬ p4253) ∨ (¬ p4391) ∨ (¬ p4236) ∨ (¬ p4781) ∨ (¬ p3461) ∨ p2630 ∨ (¬ p3564) ∨ (¬ p2573) ∨ (¬ p4419) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4253 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h46960 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step94446 (p2341 p2717 p2737 p3551 p3820 p4734 p4781 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h72735 : p4734)
    (h54107 : (¬ p2717) ∨ (¬ p2737) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p4734) ∨ (¬ p4781))
    : (¬ p2717) ∨ p2341 ∨ (¬ p2737) ∨ (¬ p4781) ∨ (¬ p3820) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3820 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4734 := h72735;
    (Or.elim h54107 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step94454 (p2598 p3434 p3516 p3820 p3821 p4752 p4781 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h60957 : (¬ p2598) ∨ (¬ p3434) ∨ (¬ p3820) ∨ (¬ p3821) ∨ (¬ p4752) ∨ (¬ p4781))
    : (¬ p3434) ∨ p3516 ∨ (¬ p2598) ∨ (¬ p4781) ∨ (¬ p3820) ∨ (¬ p4752) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3516) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3820 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h60957 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step94458 (p2307 p2761 p3309 p3549 p3654 p3946 p4381 p4396 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73492 : p3946 ∨ p3654)
    (h73406 : p3549 ∨ p3309)
    (h55967 : (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3946) ∨ (¬ p4381) ∨ (¬ p4396))
    : p2761 ∨ (¬ p2307) ∨ p3654 ∨ (¬ p4396) ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55967 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step94461 (p2761 p3461 p4381 p4396 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h19848 : (¬ p3461) ∨ (¬ p4381) ∨ (¬ p4396))
    : (¬ p3461) ∨ p2761 ∨ (¬ p4396) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h19848 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step94463 (p2295 p3246 p3319 p3922 p4026 p4396 p4559 : Prop)
    (h73504 : p4026 ∨ p3319)
    (h61766 : (¬ p2295) ∨ (¬ p3246) ∨ (¬ p3922) ∨ (¬ p4026) ∨ (¬ p4396) ∨ (¬ p4559))
    : (¬ p3922) ∨ (¬ p3246) ∨ (¬ p4559) ∨ p3319 ∨ (¬ p2295) ∨ (¬ p4396) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61766 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step94464 (p2246 p2608 p2744 p3093 p3266 p3286 p3319 p3506 p3591 p4026 p4396 p4444 p4669 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73504 : p4026 ∨ p3319)
    (h73432 : p3591 ∨ p3093)
    (h52824 : (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4396) ∨ (¬ p4444) ∨ (¬ p4669))
    : p3266 ∨ (¬ p3506) ∨ (¬ p4669) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p4396) ∨ p3319 ∨ (¬ p3286) ∨ p3093 ∨ (¬ p2246) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h52824 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step94470 (p2274 p3434 p3564 p4137 p4203 p4361 p4396 p4777 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h55851 : (¬ p2274) ∨ (¬ p3434) ∨ (¬ p4137) ∨ (¬ p4203) ∨ (¬ p4361) ∨ (¬ p4396) ∨ (¬ p4777))
    : (¬ p3434) ∨ p3564 ∨ (¬ p2274) ∨ (¬ p4396) ∨ (¬ p4361) ∨ (¬ p4777) ∨ (¬ p4203) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4777 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h55851 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step94475 (p2122 p2246 p2307 p2313 p2744 p2778 p3266 p3286 p3366 p3506 p3917 p4396 p4444 p4669 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73238 : p2313 ∨ p2307)
    (h61844 : (¬ p2122) ∨ (¬ p2246) ∨ (¬ p2313) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p3286) ∨ (¬ p3366) ∨ (¬ p3506) ∨ (¬ p3917) ∨ (¬ p4396) ∨ (¬ p4444) ∨ (¬ p4669))
    : p3266 ∨ (¬ p2246) ∨ (¬ p2778) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p4669) ∨ p2307 ∨ (¬ p4396) ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p2122) ∨ (¬ p3917) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u13 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h61844 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u13))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u7))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u12))) (fun r10 => (False.elim (r10 u5)))))))))))))))))))))))))

theorem step94478 (p2264 p2341 p3016 p3553 p4109 p4112 p4717 p4988 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h56759 : (¬ p2341) ∨ (¬ p3016) ∨ (¬ p3553) ∨ (¬ p4109) ∨ (¬ p4112) ∨ (¬ p4717) ∨ (¬ p4988))
    : (¬ p2341) ∨ (¬ p4988) ∨ (¬ p4109) ∨ (¬ p4112) ∨ p2264 ∨ (¬ p3016) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4112 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56759 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u1)))))))))))))))

theorem step94484 (p2553 p4710 p5876 : Prop)
    (h74175 : (¬ p2553) ∨ (¬ p5876))
    (h12246 : p4710 ∨ p5876)
    : p4710 ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4710) := (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5876) := (Or.elim h74175 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12246 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step94485 (p2553 p3920 p5876 : Prop)
    (h74175 : (¬ p2553) ∨ (¬ p5876))
    (h12247 : p3920 ∨ p5876)
    : p3920 ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3920) := (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5876) := (Or.elim h74175 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12247 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step94490 (p2156 p2274 p3309 p3549 p4512 p4525 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h52337 : (¬ p2156) ∨ (¬ p2274) ∨ (¬ p3549) ∨ (¬ p4512) ∨ (¬ p4525))
    : (¬ p4512) ∨ p3309 ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p4525) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4512 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3309) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4525 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h52337 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step94491 (p2210 p2274 p2498 p2553 p2588 p3379 p3555 p4512 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73282 : p2588 ∨ p2553)
    (h47504 : (¬ p2274) ∨ (¬ p2498) ∨ (¬ p2588) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4512))
    : p2210 ∨ (¬ p2274) ∨ (¬ p3379) ∨ (¬ p2498) ∨ (¬ p4512) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2498 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h47504 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step94492 (p2274 p2563 p3309 p3549 p4512 p4629 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h61082 : (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3549) ∨ (¬ p4512) ∨ (¬ p4629))
    : (¬ p4512) ∨ p3309 ∨ (¬ p2274) ∨ (¬ p4629) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4512 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3309) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h61082 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step94500 (p2307 p2608 p3309 p3549 p3954 p4512 p4877 p5020 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73406 : p3549 ∨ p3309)
    (h41166 : (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3954) ∨ (¬ p4512) ∨ (¬ p4877) ∨ (¬ p5020))
    : p2608 ∨ p3309 ∨ (¬ p5020) ∨ (¬ p4877) ∨ (¬ p4512) ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3309) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41166 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step94501 (p2166 p2274 p3309 p3549 p4509 p4512 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h56419 : (¬ p2166) ∨ (¬ p2274) ∨ (¬ p3549) ∨ (¬ p4509) ∨ (¬ p4512))
    : p3309 ∨ (¬ p2274) ∨ (¬ p2166) ∨ (¬ p4512) ∨ (¬ p4509) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3309) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h56419 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step94502 (p2166 p2307 p3309 p3549 p3743 p4509 p4512 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h62015 : (¬ p2166) ∨ (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3743) ∨ (¬ p4509) ∨ (¬ p4512))
    : (¬ p2307) ∨ p3309 ∨ (¬ p3743) ∨ (¬ p4509) ∨ (¬ p4512) ∨ (¬ p2166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3309) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h62015 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step94514 (p2891 p3319 p3654 p3743 p4026 p4512 p4558 : Prop)
    (h73504 : p4026 ∨ p3319)
    (h50968 : (¬ p2891) ∨ (¬ p3654) ∨ (¬ p3743) ∨ (¬ p4026) ∨ (¬ p4512) ∨ (¬ p4558))
    : (¬ p3654) ∨ p3319 ∨ (¬ p4512) ∨ (¬ p2891) ∨ (¬ p3743) ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3319) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h50968 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step94526 (p2274 p2972 p3309 p3549 p4512 p5046 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h57736 : (¬ p2274) ∨ (¬ p2972) ∨ (¬ p3549) ∨ (¬ p4512) ∨ (¬ p5046))
    : p3309 ∨ (¬ p2274) ∨ (¬ p2972) ∨ (¬ p4512) ∨ (¬ p5046) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3309) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5046 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h57736 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step94527 (p3016 p3319 p3564 p4026 p4202 p4512 p4811 : Prop)
    (h73504 : p4026 ∨ p3319)
    (h49058 : (¬ p3016) ∨ (¬ p3564) ∨ (¬ p4026) ∨ (¬ p4202) ∨ (¬ p4512) ∨ (¬ p4811))
    : (¬ p3564) ∨ p3319 ∨ (¬ p4512) ∨ (¬ p3016) ∨ (¬ p4811) ∨ (¬ p4202) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3319) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h49058 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step94536 (p2753 p3093 p3276 p3286 p3399 p3506 p3631 p3817 p4117 p4366 p4425 p4512 p4638 p4877 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73570 : p4366 ∨ p3399)
    (h73468 : p3817 ∨ p3631)
    (h51311 : (¬ p2753) ∨ (¬ p3093) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p3817) ∨ (¬ p4117) ∨ (¬ p4366) ∨ (¬ p4425) ∨ (¬ p4512) ∨ (¬ p4638) ∨ (¬ p4877))
    : p3276 ∨ p3399 ∨ (¬ p4877) ∨ (¬ p3093) ∨ p3631 ∨ (¬ p4512) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p2753) ∨ (¬ p4117) ∨ (¬ p4638) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4638 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u13 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51311 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u13))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (False.elim (r9 u2)))))))))))))))))))))))

theorem step94537 (p2241 p2247 p2881 p2891 p3093 p4512 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h47465 : (¬ p2247) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3093) ∨ (¬ p4512))
    : p2241 ∨ (¬ p3093) ∨ (¬ p4512) ∨ (¬ p2891) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h47465 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step94539 (p2901 p3125 p3319 p4026 p4282 p4512 p4558 : Prop)
    (h73504 : p4026 ∨ p3319)
    (h49402 : (¬ p2901) ∨ (¬ p3125) ∨ (¬ p4026) ∨ (¬ p4282) ∨ (¬ p4512) ∨ (¬ p4558))
    : (¬ p3125) ∨ (¬ p4282) ∨ (¬ p4558) ∨ (¬ p2901) ∨ p3319 ∨ (¬ p4512) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49402 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step94544 (p2187 p2274 p3097 p3136 p3923 p4282 p4315 p4512 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73550 : p4315 ∨ p3136)
    (h63942 : (¬ p2187) ∨ (¬ p3097) ∨ (¬ p3923) ∨ (¬ p4282) ∨ (¬ p4315) ∨ (¬ p4512))
    : (¬ p4282) ∨ p2274 ∨ (¬ p4512) ∨ (¬ p3923) ∨ p3136 ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4282 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63942 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step94545 (p2315 p2341 p2363 p2459 p3325 p3551 p4348 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73562 : p4348 ∨ p2459)
    (h41435 : (¬ p2315) ∨ (¬ p2363) ∨ (¬ p3325) ∨ (¬ p3551) ∨ (¬ p4348))
    : p2341 ∨ (¬ p3325) ∨ (¬ p2315) ∨ (¬ p2363) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41435 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step94552 (p2440 p2542 p2659 p2870 p3051 p3556 p3698 p3904 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73270 : p2542 ∨ p2440)
    (h42468 : (¬ p2542) ∨ (¬ p2659) ∨ (¬ p2870) ∨ (¬ p3556) ∨ (¬ p3698) ∨ (¬ p3904))
    : (¬ p2870) ∨ p3051 ∨ (¬ p3904) ∨ (¬ p3698) ∨ p2440 ∨ (¬ p2659) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42468 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step94554 (p2220 p2363 p3904 p3979 p4120 p4347 p5568 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h73560 : p4347 ∨ p2363)
    (h46456 : (¬ p3904) ∨ (¬ p3979) ∨ (¬ p4120) ∨ (¬ p4347) ∨ (¬ p5568))
    : (¬ p3979) ∨ (¬ p5568) ∨ (¬ p3904) ∨ p2220 ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3979 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46456 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step94555 (p2641 p2662 p2891 p3051 p3556 p3904 p4154 p4365 p4972 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73414 : p3556 ∨ p3051)
    (h64225 : (¬ p2662) ∨ (¬ p2891) ∨ (¬ p3556) ∨ (¬ p3904) ∨ (¬ p4154) ∨ (¬ p4365) ∨ (¬ p4972))
    : (¬ p4365) ∨ p2641 ∨ (¬ p3904) ∨ (¬ p2891) ∨ (¬ p4972) ∨ (¬ p2662) ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4365 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h64225 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step94557 (p2156 p2192 p2662 p2996 p3646 p3904 p4365 p4650 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h41506 : (¬ p2192) ∨ (¬ p2662) ∨ (¬ p2996) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4365) ∨ (¬ p4650))
    : (¬ p2996) ∨ (¬ p4650) ∨ p2156 ∨ (¬ p3904) ∨ (¬ p2192) ∨ (¬ p2662) ∨ (¬ p4365) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41506 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u1)))))))))))))))

theorem step94560 (p2573 p2751 p2951 p2992 p3364 p3422 p3584 p3904 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h64794 : (¬ p2573) ∨ (¬ p2751) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3364) ∨ (¬ p3584) ∨ (¬ p3904))
    : (¬ p2951) ∨ (¬ p2992) ∨ p3422 ∨ (¬ p3364) ∨ (¬ p2573) ∨ (¬ p3904) ∨ (¬ p2751) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2951 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h64794 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step94561 (p2331 p2427 p2982 p3051 p3461 p3506 p3556 p3904 p4117 p4191 p4368 p4421 p4729 p4948 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73846 : p4948 ∨ p2982)
    (h73414 : p3556 ∨ p3051)
    (h58168 : (¬ p2331) ∨ (¬ p2427) ∨ (¬ p3506) ∨ (¬ p3556) ∨ (¬ p3904) ∨ (¬ p4117) ∨ (¬ p4191) ∨ (¬ p4368) ∨ (¬ p4421) ∨ (¬ p4729) ∨ (¬ p4948))
    : p3461 ∨ (¬ p3506) ∨ (¬ p3904) ∨ (¬ p4421) ∨ (¬ p4368) ∨ p2982 ∨ (¬ p2427) ∨ (¬ p4729) ∨ (¬ p2331) ∨ p3051 ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4421 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h58168 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u13))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u7))) (fun r9 => (False.elim (r9 u12)))))))))))))))))))))))

theorem step94563 (p2331 p3166 p3172 p4349 p4421 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h23609 : (¬ p2331) ∨ (¬ p3172) ∨ (¬ p4349) ∨ (¬ p4421))
    : (¬ p4349) ∨ p3166 ∨ (¬ p4421) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4349 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4421 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h23609 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step94564 (p3309 p3549 p3707 p4349 p4405 p4417 p5153 p5284 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h42007 : (¬ p3549) ∨ (¬ p3707) ∨ (¬ p4349) ∨ (¬ p4405) ∨ (¬ p4417) ∨ (¬ p5153) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p3707) ∨ p3309 ∨ (¬ p4349) ∨ (¬ p4405) ∨ (¬ p5153) ∨ (¬ p4417) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4349 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42007 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u0)))))))))))))))

theorem step94567 (p2417 p2911 p3146 p4278 p4660 p4905 p5107 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h53192 : (¬ p2911) ∨ (¬ p3146) ∨ (¬ p4278) ∨ (¬ p4660) ∨ (¬ p4905) ∨ (¬ p5107))
    : p2417 ∨ (¬ p5107) ∨ (¬ p4905) ∨ (¬ p3146) ∨ (¬ p4660) ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p5107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h53192 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step94568 (p2528 p3166 p3286 p3292 p5009 p5107 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h41440 : (¬ p2528) ∨ (¬ p3166) ∨ (¬ p3292) ∨ (¬ p5009) ∨ (¬ p5107))
    : p3286 ∨ (¬ p5107) ∨ (¬ p3166) ∨ (¬ p2528) ∨ (¬ p5009) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3286) := (fun h => hn (Or.inl h));
    let u1 : p5107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5009 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41440 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step94577 (p2264 p2341 p2427 p3553 p3691 p4386 p4702 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h41495 : (¬ p2341) ∨ (¬ p2427) ∨ (¬ p3553) ∨ (¬ p3691) ∨ (¬ p4386) ∨ (¬ p4702))
    : (¬ p2341) ∨ (¬ p3691) ∨ (¬ p4702) ∨ p2264 ∨ (¬ p4386) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41495 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step94579 (p2341 p2441 p2901 p2911 p3644 p3691 p4705 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h54331 : (¬ p2341) ∨ (¬ p2441) ∨ (¬ p2901) ∨ (¬ p3644) ∨ (¬ p3691) ∨ (¬ p4705))
    : (¬ p2901) ∨ (¬ p3691) ∨ p2911 ∨ (¬ p2341) ∨ (¬ p2441) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h54331 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step94584 (p2341 p2441 p2870 p2911 p3644 p3691 p4885 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h41703 : (¬ p2341) ∨ (¬ p2441) ∨ (¬ p2870) ∨ (¬ p3644) ∨ (¬ p3691) ∨ (¬ p4885))
    : (¬ p2870) ∨ (¬ p2341) ∨ (¬ p4885) ∨ (¬ p3691) ∨ (¬ p2441) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41703 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step94586 (p2449 p2870 p3516 p3691 p3947 p4386 p5053 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h41360 : (¬ p2870) ∨ (¬ p3516) ∨ (¬ p3691) ∨ (¬ p3947) ∨ (¬ p4386) ∨ (¬ p5053))
    : (¬ p3516) ∨ p2449 ∨ (¬ p5053) ∨ (¬ p4386) ∨ (¬ p3691) ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41360 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step94589 (p2192 p3073 p3146 p4261 p4492 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h69539 : (¬ p4261) ∨ (¬ p4492) ∨ (¬ p2192) ∨ (¬ p3146))
    : p3073 ∨ (¬ p4492) ∨ (¬ p3146) ∨ (¬ p2192) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p4492 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h69539 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step94594 (p2210 p3449 p3555 p4492 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h20083 : (¬ p3449) ∨ (¬ p3555) ∨ (¬ p4492))
    : (¬ p3449) ∨ p2210 ∨ (¬ p4492) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4492 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h20083 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step94597 (p2088 p2427 p3073 p3691 p4261 p4492 p4590 p4629 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h42542 : (¬ p2088) ∨ (¬ p2427) ∨ (¬ p3691) ∨ (¬ p4261) ∨ (¬ p4492) ∨ (¬ p4590) ∨ (¬ p4629))
    : p3073 ∨ (¬ p4590) ∨ (¬ p3691) ∨ (¬ p4629) ∨ (¬ p2427) ∨ (¬ p4492) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p4590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4492 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42542 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step94602 (p2192 p2220 p2553 p2588 p2598 p3055 p3073 p3146 p3422 p3584 p4172 p4261 p4492 p4736 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h73282 : p2588 ∨ p2553)
    (h73350 : p3055 ∨ p2598)
    (h73544 : p4261 ∨ p3073)
    (h59878 : (¬ p2192) ∨ (¬ p2220) ∨ (¬ p2588) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3584) ∨ (¬ p4172) ∨ (¬ p4261) ∨ (¬ p4492) ∨ (¬ p4736))
    : p3422 ∨ (¬ p2220) ∨ p2553 ∨ (¬ p4736) ∨ (¬ p3146) ∨ (¬ p4492) ∨ (¬ p4172) ∨ (¬ p2192) ∨ p2598 ∨ p3073 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4492 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u13 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h59878 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u13))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step94604 (p2088 p3073 p3156 p3696 p4261 p4492 p4957 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h41666 : (¬ p2088) ∨ (¬ p3156) ∨ (¬ p3696) ∨ (¬ p4261) ∨ (¬ p4492) ∨ (¬ p4957))
    : p3073 ∨ (¬ p2088) ∨ (¬ p3156) ∨ (¬ p3696) ∨ (¬ p4957) ∨ (¬ p4492) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4492 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41666 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step94605 (p2088 p2891 p3073 p3743 p4114 p4261 p4492 p4558 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h51195 : (¬ p2088) ∨ (¬ p2891) ∨ (¬ p3743) ∨ (¬ p4114) ∨ (¬ p4261) ∨ (¬ p4492) ∨ (¬ p4558))
    : (¬ p4114) ∨ p3073 ∨ (¬ p3743) ∨ (¬ p4558) ∨ (¬ p4492) ∨ (¬ p2088) ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4114 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4492 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h51195 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step94609 (p2510 p2528 p2891 p3073 p3096 p4261 p4492 p4558 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h56001 : (¬ p2510) ∨ (¬ p2528) ∨ (¬ p2891) ∨ (¬ p3096) ∨ (¬ p4261) ∨ (¬ p4492) ∨ (¬ p4558))
    : p3073 ∨ (¬ p4558) ∨ (¬ p2510) ∨ (¬ p4492) ∨ (¬ p2891) ∨ (¬ p2528) ∨ (¬ p3096) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2510 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4492 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h56001 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u1)))))))))))))))

theorem step94611 (p2982 p3440 p3680 p3707 p4321 p4492 p4629 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h42005 : (¬ p2982) ∨ (¬ p3440) ∨ (¬ p3680) ∨ (¬ p4321) ∨ (¬ p4492) ∨ (¬ p4629))
    : p3707 ∨ (¬ p3440) ∨ (¬ p3680) ∨ (¬ p4492) ∨ (¬ p2982) ∨ (¬ p4629) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : p3440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4492 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42005 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step94626 (p3319 p3323 p3979 p4037 p4371 p5693 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h56574 : (¬ p3319) ∨ (¬ p3979) ∨ (¬ p4037) ∨ (¬ p4371) ∨ (¬ p5693))
    : (¬ p5693) ∨ (¬ p3319) ∨ (¬ p4371) ∨ p3323 ∨ (¬ p3979) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5693 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56574 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step94628 (p2210 p3156 p3449 p3860 p3906 p4957 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h65092 : (¬ p2210) ∨ (¬ p3156) ∨ (¬ p3860) ∨ (¬ p3906) ∨ (¬ p4957))
    : p3449 ∨ (¬ p3906) ∨ (¬ p4957) ∨ (¬ p3156) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3449) := (fun h => hn (Or.inl h));
    let u1 : p3906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h65092 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step94629 (p2210 p2449 p2685 p2696 p2753 p3146 p3449 p3692 p3860 p3906 p3950 p4877 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73482 : p3860 ∨ p3449)
    (h51347 : (¬ p2210) ∨ (¬ p2449) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3692) ∨ (¬ p3860) ∨ (¬ p3906) ∨ (¬ p3950) ∨ (¬ p4877))
    : (¬ p2449) ∨ p3146 ∨ (¬ p2753) ∨ (¬ p2210) ∨ (¬ p2685) ∨ (¬ p3906) ∨ (¬ p2696) ∨ p3449 ∨ (¬ p3950) ∨ (¬ p4877) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h51347 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step94631 (p2210 p2363 p3146 p3449 p3692 p3860 p3906 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h73448 : p3692 ∨ p3146)
    (h60857 : (¬ p2210) ∨ (¬ p2363) ∨ (¬ p3692) ∨ (¬ p3860) ∨ (¬ p3906))
    : p3449 ∨ p3146 ∨ (¬ p2363) ∨ (¬ p2210) ∨ (¬ p3906) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3449) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h60857 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step94633 (p2363 p2608 p3146 p3449 p3692 p3860 p3906 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73482 : p3860 ∨ p3449)
    (h53965 : (¬ p2363) ∨ (¬ p2608) ∨ (¬ p3692) ∨ (¬ p3860) ∨ (¬ p3906))
    : p3146 ∨ (¬ p3906) ∨ (¬ p2363) ∨ (¬ p2608) ∨ p3449 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p3906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h53965 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step94640 (p2088 p2143 p2641 p2668 p2696 p2742 p2839 p3146 p3583 p3697 p3857 p4134 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73480 : p3857 ∨ p2088)
    (h72069 : (¬ p3583) ∨ (¬ p2143) ∨ (¬ p4134) ∨ (¬ p2668) ∨ (¬ p3857) ∨ (¬ p2696) ∨ (¬ p3146) ∨ (¬ p3697) ∨ (¬ p2641) ∨ (¬ p2742))
    : (¬ p2668) ∨ (¬ p2742) ∨ (¬ p4134) ∨ p2839 ∨ (¬ p3146) ∨ p2088 ∨ (¬ p2696) ∨ (¬ p2143) ∨ (¬ p2641) ∨ (¬ p3697) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h72069 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u1)))))))))))))))))))))

theorem step94641 (p2088 p2954 p3146 p3156 p3697 p3857 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h42303 : (¬ p2954) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3697) ∨ (¬ p3857))
    : p2088 ∨ (¬ p3146) ∨ (¬ p2954) ∨ (¬ p3697) ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2088) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42303 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step94643 (p2088 p2850 p3146 p3684 p3697 p3857 p4031 p5568 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h73442 : p3684 ∨ p2850)
    (h58085 : (¬ p3146) ∨ (¬ p3684) ∨ (¬ p3697) ∨ (¬ p3857) ∨ (¬ p4031) ∨ (¬ p5568))
    : (¬ p5568) ∨ (¬ p4031) ∨ (¬ p3697) ∨ p2088 ∨ p2850 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5568 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h58085 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step94644 (p2088 p2373 p3146 p3697 p3857 p4533 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h41626 : (¬ p2373) ∨ (¬ p3146) ∨ (¬ p3697) ∨ (¬ p3857) ∨ (¬ p4533))
    : (¬ p3697) ∨ p2088 ∨ (¬ p4533) ∨ (¬ p2373) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3697 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2088) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41626 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step94651 (p2088 p2510 p2528 p3051 p3096 p3697 p3857 p4558 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h49766 : (¬ p2510) ∨ (¬ p2528) ∨ (¬ p3051) ∨ (¬ p3096) ∨ (¬ p3697) ∨ (¬ p3857) ∨ (¬ p4558))
    : (¬ p2510) ∨ (¬ p3697) ∨ p2088 ∨ (¬ p4558) ∨ (¬ p2528) ∨ (¬ p3096) ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2510 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h49766 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step94655 (p2470 p2663 p2946 p2952 p3016 p3573 p3574 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73422 : p3574 ∨ p3016)
    (h69687 : (¬ p2470) ∨ (¬ p2952) ∨ (¬ p3574) ∨ (¬ p3573) ∨ (¬ p2663))
    : (¬ p2470) ∨ p2946 ∨ (¬ p2663) ∨ p3016 ∨ (¬ p3573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69687 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step94656 (p2363 p2528 p2534 p2630 p2810 p3016 p3573 p3574 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73316 : p2810 ∨ p2630)
    (h73422 : p3574 ∨ p3016)
    (h62319 : (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2810) ∨ (¬ p3573) ∨ (¬ p3574))
    : p2528 ∨ (¬ p2363) ∨ p2630 ∨ p3016 ∨ (¬ p3573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62319 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step94659 (p2363 p2528 p2534 p2573 p2579 p2662 p2727 p3573 p4111 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73518 : p4111 ∨ p2727)
    (h73274 : p2579 ∨ p2573)
    (h56766 : (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2579) ∨ (¬ p2662) ∨ (¬ p3573) ∨ (¬ p4111))
    : p2528 ∨ p2727 ∨ (¬ p3573) ∨ p2573 ∨ (¬ p2363) ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56766 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step94661 (p2363 p2528 p2534 p3573 p3888 p5586 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h42236 : (¬ p2363) ∨ (¬ p2534) ∨ (¬ p3573) ∨ (¬ p3888) ∨ (¬ p5586))
    : (¬ p3888) ∨ p2528 ∨ (¬ p3573) ∨ (¬ p5586) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3888 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5586 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42236 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step94662 (p2363 p2493 p2499 p2528 p2534 p3379 p3452 p3573 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73394 : p3452 ∨ p3379)
    (h73268 : p2534 ∨ p2528)
    (h44179 : (¬ p2363) ∨ (¬ p2499) ∨ (¬ p2534) ∨ (¬ p3452) ∨ (¬ p3573))
    : p2493 ∨ p3379 ∨ (¬ p2363) ∨ (¬ p3573) ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2493) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h44179 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step94670 (p2187 p2553 p3573 p3979 p4149 p4286 : Prop)
    (h73548 : p4286 ∨ p4149)
    (h65210 : (¬ p2187) ∨ (¬ p2553) ∨ (¬ p3573) ∨ (¬ p3979) ∨ (¬ p4286))
    : p4149 ∨ (¬ p3979) ∨ (¬ p2187) ∨ (¬ p2553) ∨ (¬ p3573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4149) := (fun h => hn (Or.inl h));
    let u1 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4286 := (Or.elim h73548 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h65210 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step94672 (p2553 p2651 p2657 p2727 p3005 p3361 p3573 p4346 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h64592 : (¬ p2553) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p3005) ∨ (¬ p3361) ∨ (¬ p3573) ∨ (¬ p4346))
    : (¬ p2727) ∨ (¬ p2553) ∨ (¬ p3573) ∨ (¬ p3005) ∨ (¬ p4346) ∨ (¬ p3361) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h64592 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step94674 (p2331 p2553 p2588 p2963 p3888 p5717 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73282 : p2588 ∨ p2553)
    (h44392 : (¬ p2588) ∨ (¬ p2963) ∨ (¬ p3888) ∨ (¬ p5717))
    : (¬ p3888) ∨ (¬ p5717) ∨ p2331 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3888 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44392 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step94675 (p2241 p2247 p2641 p2761 p3051 p3246 p4154 p4521 p5254 p5717 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73526 : p4154 ∨ p2641)
    (h55769 : (¬ p2247) ∨ (¬ p2761) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p4154) ∨ (¬ p4521) ∨ (¬ p5254) ∨ (¬ p5717))
    : (¬ p5717) ∨ (¬ p2761) ∨ (¬ p3051) ∨ (¬ p3246) ∨ p2241 ∨ p2641 ∨ (¬ p5254) ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h55769 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step94677 (p2331 p2630 p2810 p2963 p3914 p4426 p5717 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73316 : p2810 ∨ p2630)
    (h46670 : (¬ p2810) ∨ (¬ p2963) ∨ (¬ p3914) ∨ (¬ p4426) ∨ (¬ p5717))
    : (¬ p3914) ∨ (¬ p5717) ∨ (¬ p4426) ∨ p2331 ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3914 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46670 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step94681 (p2696 p2761 p2797 p3073 p3365 p3449 p4195 p4445 p4736 p5254 p5717 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73390 : p3365 ∨ p2696)
    (h64574 : (¬ p2761) ∨ (¬ p3073) ∨ (¬ p3365) ∨ (¬ p3449) ∨ (¬ p4195) ∨ (¬ p4445) ∨ (¬ p4736) ∨ (¬ p5254) ∨ (¬ p5717))
    : (¬ p5717) ∨ (¬ p4445) ∨ (¬ p5254) ∨ p2797 ∨ (¬ p3449) ∨ (¬ p3073) ∨ p2696 ∨ (¬ p4736) ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h64574 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step94682 (p2797 p3755 p4195 p4367 p5249 p5717 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h50555 : (¬ p3755) ∨ (¬ p4195) ∨ (¬ p4367) ∨ (¬ p5249) ∨ (¬ p5717))
    : (¬ p3755) ∨ (¬ p5717) ∨ p2797 ∨ (¬ p4367) ∨ (¬ p5249) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50555 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step94683 (p2751 p2797 p4053 p4195 p4759 p5717 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h41746 : (¬ p2751) ∨ (¬ p4053) ∨ (¬ p4195) ∨ (¬ p4759) ∨ (¬ p5717))
    : (¬ p5717) ∨ (¬ p4053) ∨ (¬ p2751) ∨ (¬ p4759) ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41746 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step94684 (p2440 p2542 p3888 p4194 p4715 p5717 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h50364 : (¬ p2542) ∨ (¬ p3888) ∨ (¬ p4194) ∨ (¬ p4715) ∨ (¬ p5717))
    : (¬ p3888) ∨ (¬ p5717) ∨ (¬ p4194) ∨ (¬ p4715) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3888 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50364 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step94685 (p2241 p2247 p2641 p2761 p3425 p3434 p3471 p4154 p4733 p5254 p5717 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73226 : p2247 ∨ p2241)
    (h73396 : p3471 ∨ p3425)
    (h51550 : (¬ p2247) ∨ (¬ p2761) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p4154) ∨ (¬ p4733) ∨ (¬ p5254) ∨ (¬ p5717))
    : p2641 ∨ p2241 ∨ (¬ p2761) ∨ (¬ p4733) ∨ (¬ p3434) ∨ p3425 ∨ (¬ p5254) ∨ (¬ p5717) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h51550 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step94688 (p2696 p2761 p2797 p3051 p3246 p3365 p3366 p3370 p4195 p4377 p5254 p5717 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73390 : p3365 ∨ p2696)
    (h42582 : (¬ p2761) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p4195) ∨ (¬ p4377) ∨ (¬ p5254) ∨ (¬ p5717))
    : (¬ p3051) ∨ (¬ p3246) ∨ (¬ p2761) ∨ (¬ p5717) ∨ (¬ p4377) ∨ p2797 ∨ (¬ p3366) ∨ p2696 ∨ (¬ p3370) ∨ (¬ p5254) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h42582 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step94690 (p2668 p3324 p4228 p4503 p5558 p5584 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h55522 : (¬ p3324) ∨ (¬ p4228) ∨ (¬ p4503) ∨ (¬ p5558) ∨ (¬ p5584))
    : (¬ p4228) ∨ (¬ p5558) ∨ (¬ p5584) ∨ p2668 ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4228 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55522 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step94692 (p2187 p3737 p3989 p4503 p5558 p5584 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h57916 : (¬ p3737) ∨ (¬ p3989) ∨ (¬ p4503) ∨ (¬ p5558) ∨ (¬ p5584))
    : (¬ p3737) ∨ (¬ p5558) ∨ (¬ p4503) ∨ p2187 ∨ (¬ p5584) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h57916 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step94694 (p2352 p3888 p3956 p4771 p5584 p5600 : Prop)
    (h73500 : p3956 ∨ p2352)
    (h41508 : (¬ p3888) ∨ (¬ p3956) ∨ (¬ p4771) ∨ (¬ p5584) ∨ (¬ p5600))
    : (¬ p3888) ∨ (¬ p5600) ∨ (¬ p5584) ∨ p2352 ∨ (¬ p4771) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3888 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4771 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41508 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step94702 (p2651 p2657 p2761 p3016 p3051 p3246 p3366 p3370 p3574 p4236 p4377 p5254 p5514 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73422 : p3574 ∨ p3016)
    (h64564 : (¬ p2657) ∨ (¬ p2761) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3574) ∨ (¬ p4236) ∨ (¬ p4377) ∨ (¬ p5254) ∨ (¬ p5514))
    : (¬ p3370) ∨ (¬ p5514) ∨ (¬ p5254) ∨ p2651 ∨ (¬ p3246) ∨ (¬ p4377) ∨ (¬ p3366) ∨ (¬ p3051) ∨ (¬ p2761) ∨ p3016 ∨ (¬ p4236) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3370 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h64564 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (False.elim (r9 u1)))))))))))))))))))))))

theorem step94703 (p2341 p2696 p2797 p3146 p3266 p3365 p3366 p3370 p4132 p4195 p4377 p4988 p5254 p5717 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73390 : p3365 ∨ p2696)
    (h63574 : (¬ p2341) ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p4132) ∨ (¬ p4195) ∨ (¬ p4377) ∨ (¬ p4988) ∨ (¬ p5254) ∨ (¬ p5717))
    : (¬ p5717) ∨ (¬ p3370) ∨ (¬ p4132) ∨ (¬ p3366) ∨ (¬ p5254) ∨ (¬ p3266) ∨ (¬ p3146) ∨ (¬ p2341) ∨ (¬ p4377) ∨ p2797 ∨ (¬ p4988) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u13 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    (Or.elim h63574 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u13))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u4))) (fun r10 => (False.elim (r10 u0)))))))))))))))))))))))))

theorem step94706 (p2248 p2493 p2499 p3166 p3256 p3266 p3379 p3452 p5254 p5514 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73260 : p2499 ∨ p2493)
    (h60581 : (¬ p2248) ∨ (¬ p2499) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3452) ∨ (¬ p5254) ∨ (¬ p5514))
    : p3379 ∨ (¬ p5514) ∨ (¬ p3166) ∨ p2493 ∨ (¬ p3266) ∨ (¬ p2248) ∨ (¬ p5254) ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60581 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step94707 (p2493 p2499 p2761 p3051 p3246 p3379 p3452 p4521 p5254 p5514 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73394 : p3452 ∨ p3379)
    (h41567 : (¬ p2499) ∨ (¬ p2761) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3452) ∨ (¬ p4521) ∨ (¬ p5254) ∨ (¬ p5514))
    : (¬ p5514) ∨ (¬ p3051) ∨ (¬ p4521) ∨ (¬ p5254) ∨ (¬ p2761) ∨ p2493 ∨ (¬ p3246) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5514 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u9 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h41567 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step94708 (p2248 p2449 p2493 p2499 p2761 p2807 p3379 p3452 p5254 p5514 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73260 : p2499 ∨ p2493)
    (h48594 : (¬ p2248) ∨ (¬ p2449) ∨ (¬ p2499) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p3452) ∨ (¬ p5254) ∨ (¬ p5514))
    : (¬ p5514) ∨ p3379 ∨ (¬ p2807) ∨ (¬ p2761) ∨ p2493 ∨ (¬ p2248) ∨ (¬ p2449) ∨ (¬ p5254) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5514 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48594 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step94710 (p2284 p2341 p2459 p2946 p2952 p3266 p3952 p4393 p4850 p5254 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73330 : p2952 ∨ p2946)
    (h48029 : (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2952) ∨ (¬ p3266) ∨ (¬ p3952) ∨ (¬ p4393) ∨ (¬ p4850) ∨ (¬ p5254))
    : (¬ p4393) ∨ (¬ p3266) ∨ (¬ p4850) ∨ (¬ p2459) ∨ (¬ p2341) ∨ (¬ p5254) ∨ p2284 ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4393 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u9 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h48029 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step94714 (p2598 p3055 p3166 p3256 p3266 p3422 p3584 p4786 p5254 p5514 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h73350 : p3055 ∨ p2598)
    (h61740 : (¬ p3055) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3584) ∨ (¬ p4786) ∨ (¬ p5254) ∨ (¬ p5514))
    : p3422 ∨ (¬ p3166) ∨ (¬ p5514) ∨ (¬ p3266) ∨ (¬ p5254) ∨ p2598 ∨ (¬ p4786) ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h61740 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step94715 (p2230 p2241 p2247 p2589 p2744 p2860 p3366 p3695 p3707 p3758 p3830 p3905 p4393 p5254 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73284 : p2589 ∨ p2230)
    (h73456 : p3758 ∨ p2860)
    (h63931 : (¬ p2247) ∨ (¬ p2589) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3695) ∨ (¬ p3707) ∨ (¬ p3758) ∨ (¬ p3830) ∨ (¬ p3905) ∨ (¬ p4393) ∨ (¬ p5254))
    : (¬ p4393) ∨ p2241 ∨ (¬ p2744) ∨ (¬ p3695) ∨ (¬ p3830) ∨ p2230 ∨ (¬ p3366) ∨ p2860 ∨ (¬ p3905) ∨ (¬ p5254) ∨ (¬ p3707) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4393 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h63931 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u0))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step94724 (p2246 p2651 p2744 p2761 p3016 p3366 p3425 p3434 p3888 p4324 p4381 p5250 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73556 : p4324 ∨ p3434)
    (h61581 : (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3016) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3888) ∨ (¬ p4324) ∨ (¬ p4381) ∨ (¬ p5250))
    : (¬ p3888) ∨ p2761 ∨ (¬ p2744) ∨ (¬ p3366) ∨ p3434 ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3425) ∨ (¬ p2246) ∨ (¬ p5250) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3888 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h61581 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step94726 (p2449 p2598 p2761 p2807 p3414 p3422 p3888 p3947 p4381 p4789 p5250 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73392 : p3414 ∨ p2807)
    (h73494 : p3947 ∨ p2449)
    (h65171 : (¬ p2598) ∨ (¬ p3414) ∨ (¬ p3422) ∨ (¬ p3888) ∨ (¬ p3947) ∨ (¬ p4381) ∨ (¬ p4789) ∨ (¬ p5250))
    : p2761 ∨ (¬ p3888) ∨ p2807 ∨ (¬ p4789) ∨ p2449 ∨ (¬ p5250) ∨ (¬ p2598) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3888 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h65171 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step94727 (p2246 p2608 p2651 p2744 p3016 p3707 p3830 p3834 p3888 p4321 p5250 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h73474 : p3834 ∨ p3830)
    (h63021 : (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3016) ∨ (¬ p3834) ∨ (¬ p3888) ∨ (¬ p4321) ∨ (¬ p5250))
    : (¬ p3888) ∨ p3707 ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3016) ∨ (¬ p2246) ∨ p3830 ∨ (¬ p2651) ∨ (¬ p5250) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3888 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h63021 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step94729 (p2573 p3389 p3540 p3888 p4435 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h56302 : (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3888) ∨ (¬ p4435))
    : (¬ p3888) ∨ p3389 ∨ (¬ p4435) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3888 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h56302 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step94731 (p2437 p3016 p3742 p3888 p4329 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h43052 : (¬ p3016) ∨ (¬ p3742) ∨ (¬ p3888) ∨ (¬ p4329))
    : (¬ p3888) ∨ (¬ p4329) ∨ p2437 ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3888 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4329 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43052 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step94733 (p2284 p2373 p3660 p3880 p3888 p3952 p4393 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73490 : p3880 ∨ p2373)
    (h44116 : (¬ p3660) ∨ (¬ p3880) ∨ (¬ p3888) ∨ (¬ p3952) ∨ (¬ p4393))
    : (¬ p4393) ∨ (¬ p3888) ∨ p2284 ∨ (¬ p3660) ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4393 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3888 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h44116 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step94734 (p2427 p3660 p3888 p4235 p4393 p4555 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h58322 : (¬ p3660) ∨ (¬ p3888) ∨ (¬ p4235) ∨ (¬ p4393) ∨ (¬ p4555))
    : (¬ p4393) ∨ (¬ p3888) ∨ (¬ p4555) ∨ p2427 ∨ (¬ p3660) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4393 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3888 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h58322 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step94737 (p2252 p2449 p2504 p2608 p2750 p2761 p2807 p3093 p3414 p3888 p3947 p3954 p4381 p5250 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73392 : p3414 ∨ p2807)
    (h73498 : p3954 ∨ p2608)
    (h73494 : p3947 ∨ p2449)
    (h65230 : (¬ p2252) ∨ (¬ p2504) ∨ (¬ p2750) ∨ (¬ p3093) ∨ (¬ p3414) ∨ (¬ p3888) ∨ (¬ p3947) ∨ (¬ p3954) ∨ (¬ p4381) ∨ (¬ p5250))
    : (¬ p3888) ∨ p2761 ∨ (¬ p3093) ∨ p2807 ∨ p2608 ∨ (¬ p2750) ∨ p2449 ∨ (¬ p2504) ∨ (¬ p5250) ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3888 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u13 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h65230 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step94741 (p2307 p2553 p2588 p2696 p3365 p3366 p3755 p3888 p4035 p4866 p5016 p5250 p5284 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h73282 : p2588 ∨ p2553)
    (h73506 : p4035 ∨ p3755)
    (h64656 : (¬ p2307) ∨ (¬ p2588) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3888) ∨ (¬ p4035) ∨ (¬ p4866) ∨ (¬ p5016) ∨ (¬ p5250) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p3888) ∨ (¬ p3366) ∨ p2696 ∨ (¬ p5250) ∨ p2553 ∨ (¬ p5016) ∨ p3755 ∨ (¬ p2307) ∨ (¬ p4866) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3888 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4866 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64656 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step94745 (p3422 p3641 p3874 p3888 p4432 p5586 : Prop)
    (h73484 : p3874 ∨ p3641)
    (h42420 : (¬ p3422) ∨ (¬ p3874) ∨ (¬ p3888) ∨ (¬ p4432) ∨ (¬ p5586))
    : (¬ p3888) ∨ p3641 ∨ (¬ p4432) ∨ (¬ p5586) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3888 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5586 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42420 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step94753 (p2220 p2254 p2493 p2950 p3266 p3379 p3564 p4120 p4311 p4330 p4349 p5284 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h59520 : (¬ p2254) ∨ (¬ p2493) ∨ (¬ p2950) ∨ (¬ p3266) ∨ (¬ p3379) ∨ (¬ p3564) ∨ (¬ p4120) ∨ (¬ p4311) ∨ (¬ p4330) ∨ (¬ p4349) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p3266) ∨ p2220 ∨ (¬ p3564) ∨ (¬ p4330) ∨ (¬ p4311) ∨ (¬ p2493) ∨ (¬ p4349) ∨ (¬ p3379) ∨ (¬ p2254) ∨ (¬ p2950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4349 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h59520 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u7))) (fun r9 => (False.elim (r9 u0)))))))))))))))))))))))

theorem step94754 (p2166 p2220 p2331 p2950 p3948 p4116 p4120 p4975 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h50658 : (¬ p2166) ∨ (¬ p2331) ∨ (¬ p2950) ∨ (¬ p3948) ∨ (¬ p4116) ∨ (¬ p4120) ∨ (¬ p4975))
    : (¬ p4116) ∨ (¬ p2950) ∨ (¬ p3948) ∨ p2220 ∨ (¬ p2166) ∨ (¬ p2331) ∨ (¬ p4975) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4116 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50658 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step94757 (p2166 p2220 p2950 p3136 p3412 p4120 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h72070 : (¬ p4120) ∨ (¬ p2950) ∨ (¬ p3412) ∨ (¬ p3136) ∨ (¬ p2166))
    : (¬ p3412) ∨ (¬ p2950) ∨ p2220 ∨ (¬ p2166) ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3412 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h72070 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step94768 (p2187 p2383 p2387 p3051 p4198 p4558 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h53156 : (¬ p2187) ∨ (¬ p2387) ∨ (¬ p3051) ∨ (¬ p4198) ∨ (¬ p4558))
    : (¬ p4558) ∨ (¬ p2187) ∨ (¬ p3051) ∨ p2383 ∨ (¬ p4198) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4558 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53156 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step94770 (p2187 p2274 p2307 p2313 p2957 p3136 p3989 p4198 p4315 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73550 : p4315 ∨ p3136)
    (h73502 : p3989 ∨ p2187)
    (h46608 : (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2957) ∨ (¬ p3989) ∨ (¬ p4198) ∨ (¬ p4315))
    : p2307 ∨ (¬ p2274) ∨ p3136 ∨ (¬ p2957) ∨ p2187 ∨ (¬ p4198) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2307) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46608 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step94772 (p2274 p2307 p2313 p2563 p4198 p4533 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h60888 : (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2563) ∨ (¬ p4198) ∨ (¬ p4533))
    : p2307 ∨ (¬ p4198) ∨ (¬ p2563) ∨ (¬ p2274) ∨ (¬ p4533) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2307) := (fun h => hn (Or.inl h));
    let u1 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h60888 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step94780 (p3051 p3125 p3654 p3946 p4198 p4558 : Prop)
    (h73492 : p3946 ∨ p3654)
    (h54430 : (¬ p3051) ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p4198) ∨ (¬ p4558))
    : (¬ p3125) ∨ (¬ p4198) ∨ (¬ p4558) ∨ p3654 ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54430 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step94783 (p2295 p2307 p2313 p2668 p2850 p3324 p3684 p4031 p4198 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73386 : p3324 ∨ p2668)
    (h73442 : p3684 ∨ p2850)
    (h63285 : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p3324) ∨ (¬ p3684) ∨ (¬ p4031) ∨ (¬ p4198))
    : (¬ p4031) ∨ p2307 ∨ (¬ p4198) ∨ p2668 ∨ (¬ p2295) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4031 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h63285 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step94786 (p2274 p2440 p3097 p3125 p3654 p3946 p4031 p4198 : Prop)
    (h73492 : p3946 ∨ p3654)
    (h73352 : p3097 ∨ p2274)
    (h54471 : (¬ p2440) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p4031) ∨ (¬ p4198))
    : (¬ p4031) ∨ p3654 ∨ (¬ p3125) ∨ (¬ p2440) ∨ (¬ p4198) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4031 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3654) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h54471 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step94788 (p2088 p2954 p3146 p3156 p3857 p4197 p4198 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h41624 : (¬ p2954) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3857) ∨ (¬ p4197) ∨ (¬ p4198))
    : p2088 ∨ (¬ p4197) ∨ (¬ p3156) ∨ (¬ p2954) ∨ (¬ p3146) ∨ (¬ p4198) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2088) := (fun h => hn (Or.inl h));
    let u1 : p4197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41624 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step94793 (p2187 p2274 p2383 p2387 p2957 p2992 p3097 p3662 p4198 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73440 : p3662 ∨ p2992)
    (h73246 : p2387 ∨ p2383)
    (h43854 : (¬ p2187) ∨ (¬ p2387) ∨ (¬ p2957) ∨ (¬ p3097) ∨ (¬ p3662) ∨ (¬ p4198))
    : p2274 ∨ (¬ p2187) ∨ (¬ p2957) ∨ (¬ p4198) ∨ p2992 ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u8 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h43854 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step94797 (p2088 p2220 p2528 p3857 p4197 p4198 p4434 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h55028 : (¬ p2220) ∨ (¬ p2528) ∨ (¬ p3857) ∨ (¬ p4197) ∨ (¬ p4198) ∨ (¬ p4434))
    : (¬ p4198) ∨ (¬ p2528) ∨ (¬ p2220) ∨ p2088 ∨ (¬ p4197) ∨ (¬ p4434) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4198 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55028 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step94799 (p2187 p2274 p2307 p2313 p2957 p2992 p3662 p3989 p4198 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73440 : p3662 ∨ p2992)
    (h73502 : p3989 ∨ p2187)
    (h46597 : (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2957) ∨ (¬ p3662) ∨ (¬ p3989) ∨ (¬ p4198))
    : p2307 ∨ p2992 ∨ (¬ p2274) ∨ (¬ p2957) ∨ (¬ p4198) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2307) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h46597 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step94800 (p2274 p2307 p2313 p2957 p3156 p4198 p4509 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h48472 : (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2957) ∨ (¬ p3156) ∨ (¬ p4198) ∨ (¬ p4509))
    : (¬ p4198) ∨ (¬ p2274) ∨ (¬ p2957) ∨ (¬ p4509) ∨ p2307 ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4198 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48472 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step94805 (p2187 p2274 p2383 p2387 p2440 p3097 p4031 p4198 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73246 : p2387 ∨ p2383)
    (h63864 : (¬ p2187) ∨ (¬ p2387) ∨ (¬ p2440) ∨ (¬ p3097) ∨ (¬ p4031) ∨ (¬ p4198))
    : (¬ p4031) ∨ (¬ p2440) ∨ p2274 ∨ (¬ p4198) ∨ (¬ p2187) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4031 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h63864 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step94809 (p2352 p2383 p2387 p3276 p3461 p3746 p4198 p4425 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73246 : p2387 ∨ p2383)
    (h47590 : (¬ p2352) ∨ (¬ p2387) ∨ (¬ p3461) ∨ (¬ p3746) ∨ (¬ p4198) ∨ (¬ p4425))
    : p3276 ∨ (¬ p3746) ∨ (¬ p4198) ∨ (¬ p3461) ∨ p2383 ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3746 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47590 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step94810 (p2311 p2891 p3246 p3516 p3821 p4198 p4522 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h41761 : (¬ p2311) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3821) ∨ (¬ p4198) ∨ (¬ p4522))
    : p3516 ∨ (¬ p3246) ∨ (¬ p4198) ∨ (¬ p2311) ∨ (¬ p4522) ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4522 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41761 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step94815 (p2187 p2274 p2307 p2313 p2363 p3989 p4198 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73238 : p2313 ∨ p2307)
    (h73502 : p3989 ∨ p2187)
    (h47624 : (¬ p2274) ∨ (¬ p2313) ∨ (¬ p3989) ∨ (¬ p4198) ∨ (¬ p4347))
    : (¬ p2274) ∨ p2363 ∨ p2307 ∨ (¬ p4198) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47624 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step94819 (p2187 p2274 p2383 p2387 p2957 p3097 p3136 p4198 p4315 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73246 : p2387 ∨ p2383)
    (h73550 : p4315 ∨ p3136)
    (h63930 : (¬ p2187) ∨ (¬ p2387) ∨ (¬ p2957) ∨ (¬ p3097) ∨ (¬ p4198) ∨ (¬ p4315))
    : p2274 ∨ (¬ p2187) ∨ p2383 ∨ (¬ p2957) ∨ (¬ p4198) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h63930 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u8)))))))))))))

theorem step94821 (p2177 p2187 p2230 p2264 p2383 p2387 p2440 p2553 p2588 p2665 p3553 p3581 p3921 p3958 p4112 p4198 p4537 : Prop)
    (h73624 : p4537 ∨ (¬ p2230))
    (h73246 : p2387 ∨ p2383)
    (h73410 : p3553 ∨ p2264)
    (h73282 : p2588 ∨ p2553)
    (h66989 : (¬ p4537) ∨ (¬ p2387) ∨ (¬ p3958) ∨ (¬ p4198) ∨ (¬ p2187) ∨ (¬ p2588) ∨ (¬ p3921) ∨ (¬ p3581) ∨ (¬ p2665) ∨ (¬ p4112) ∨ (¬ p2440) ∨ (¬ p2177) ∨ (¬ p3553))
    : (¬ p2440) ∨ (¬ p2230) ∨ (¬ p4198) ∨ (¬ p2665) ∨ (¬ p2177) ∨ (¬ p3958) ∨ (¬ p4112) ∨ p2383 ∨ p2264 ∨ p2553 ∨ (¬ p3581) ∨ (¬ p3921) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4112 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : p4537 := (Or.elim h73624 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u14 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u15 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u16 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h66989 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u16))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u0))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u4))) (fun r11 => (False.elim (r11 u15)))))))))))))))))))))))))))

theorem step94822 (p2132 p2138 p3819 p3959 p4136 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h34994 : (¬ p2138) ∨ (¬ p3819) ∨ (¬ p3959) ∨ (¬ p4136))
    : p2132 ∨ (¬ p4136) ∨ (¬ p3959) ∨ (¬ p3819) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p4136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h34994 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step94823 (p3434 p3516 p3821 p3959 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h6379 : (¬ p3434) ∨ (¬ p3821) ∨ (¬ p3959))
    : p3516 ∨ (¬ p3434) ∨ (¬ p3959) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h6379 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step94828 (p2449 p2717 p2996 p3027 p3516 p3821 p3959 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73340 : p3027 ∨ p2996)
    (h45023 : (¬ p2449) ∨ (¬ p2717) ∨ (¬ p3027) ∨ (¬ p3821) ∨ (¬ p3959))
    : p3516 ∨ p2996 ∨ (¬ p2449) ∨ (¬ p3959) ∨ (¬ p2717) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45023 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step94831 (p2717 p3246 p3690 p3941 p4169 p4445 p5122 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h41331 : (¬ p2717) ∨ (¬ p3690) ∨ (¬ p3941) ∨ (¬ p4169) ∨ (¬ p4445) ∨ (¬ p5122))
    : p3246 ∨ (¬ p2717) ∨ (¬ p4169) ∨ (¬ p5122) ∨ (¬ p4445) ∨ (¬ p3941) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4169 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41331 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step94833 (p2132 p2459 p2881 p3425 p3570 p4169 p4348 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73562 : p4348 ∨ p2459)
    (h47622 : (¬ p2132) ∨ (¬ p3425) ∨ (¬ p3570) ∨ (¬ p4169) ∨ (¬ p4348))
    : p2881 ∨ p2459 ∨ (¬ p2132) ∨ (¬ p4169) ∨ (¬ p3425) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4169 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47622 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step94838 (p2363 p2427 p3073 p4169 p4189 p4253 p4347 p4442 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h64113 : (¬ p2427) ∨ (¬ p3073) ∨ (¬ p4169) ∨ (¬ p4189) ∨ (¬ p4253) ∨ (¬ p4347) ∨ (¬ p4442))
    : (¬ p4253) ∨ (¬ p4442) ∨ (¬ p4169) ∨ (¬ p2427) ∨ (¬ p3073) ∨ (¬ p4189) ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4253 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4442 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4169 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h64113 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (False.elim (r5 u1)))))))))))))))

theorem step94839 (p2717 p2881 p2891 p3659 p4136 p4878 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h49226 : (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3659) ∨ (¬ p4136) ∨ (¬ p4878))
    : (¬ p2891) ∨ (¬ p2881) ∨ (¬ p4878) ∨ p2717 ∨ (¬ p4136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4878 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49226 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step94840 (p2132 p2138 p2707 p3366 p4136 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h20292 : (¬ p2138) ∨ (¬ p2707) ∨ (¬ p3366) ∨ (¬ p4136))
    : (¬ p2707) ∨ p2132 ∨ (¬ p4136) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h20292 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step94842 (p2132 p2138 p3425 p3471 p4136 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73396 : p3471 ∨ p3425)
    (h20417 : (¬ p2138) ∨ (¬ p3471) ∨ (¬ p4136))
    : p2132 ∨ (¬ p4136) ∨ p3425 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p4136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20417 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u1)))))))

theorem step94849 (p2860 p3246 p3576 p3631 p3817 p4136 p4555 : Prop)
    (h73468 : p3817 ∨ p3631)
    (h41258 : (¬ p2860) ∨ (¬ p3246) ∨ (¬ p3576) ∨ (¬ p3817) ∨ (¬ p4136) ∨ (¬ p4555))
    : (¬ p3576) ∨ p3631 ∨ (¬ p4555) ∨ (¬ p2860) ∨ (¬ p4136) ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3576 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3631) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41258 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step94850 (p2860 p3246 p3434 p4136 p4324 p4555 : Prop)
    (h73556 : p4324 ∨ p3434)
    (h42009 : (¬ p2860) ∨ (¬ p3246) ∨ (¬ p4136) ∨ (¬ p4324) ∨ (¬ p4555))
    : (¬ p4136) ∨ p3434 ∨ (¬ p2860) ∨ (¬ p3246) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3434) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42009 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step94851 (p2136 p2860 p3051 p3425 p3471 p3556 p4136 p4555 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73396 : p3471 ∨ p3425)
    (h42047 : (¬ p2136) ∨ (¬ p2860) ∨ (¬ p3471) ∨ (¬ p3556) ∨ (¬ p4136) ∨ (¬ p4555))
    : (¬ p4136) ∨ p3051 ∨ (¬ p4555) ∨ (¬ p2860) ∨ (¬ p2136) ∨ p3425 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h42047 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step94857 (p3051 p3246 p3434 p4136 p4324 : Prop)
    (h73556 : p4324 ∨ p3434)
    (h72073 : (¬ p4324) ∨ (¬ p3246) ∨ (¬ p4136) ∨ (¬ p3051))
    : (¬ p3246) ∨ p3434 ∨ (¬ p4136) ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3434) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h72073 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step94860 (p2619 p3246 p3434 p3872 p4136 p4324 p4509 : Prop)
    (h73556 : p4324 ∨ p3434)
    (h50614 : (¬ p2619) ∨ (¬ p3246) ∨ (¬ p3872) ∨ (¬ p4136) ∨ (¬ p4324) ∨ (¬ p4509))
    : (¬ p2619) ∨ (¬ p3246) ∨ p3434 ∨ (¬ p4509) ∨ (¬ p3872) ∨ (¬ p4136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50614 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step94870 (p2427 p3246 p3434 p4136 p4324 p4882 : Prop)
    (h73556 : p4324 ∨ p3434)
    (h63948 : (¬ p2427) ∨ (¬ p3246) ∨ (¬ p4136) ∨ (¬ p4324) ∨ (¬ p4882))
    : (¬ p3246) ∨ (¬ p4136) ∨ (¬ p2427) ∨ (¬ p4882) ∨ p3434 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4882 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63948 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step94873 (p2241 p2247 p2744 p3516 p3545 p3554 p3631 p3817 p4874 : Prop)
    (h73468 : p3817 ∨ p3631)
    (h73226 : p2247 ∨ p2241)
    (h52789 : (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3516) ∨ (¬ p3545) ∨ (¬ p3554) ∨ (¬ p3817) ∨ (¬ p4874))
    : p3631 ∨ p2241 ∨ (¬ p2744) ∨ (¬ p4874) ∨ (¬ p3516) ∨ (¬ p3545) ∨ (¬ p3554) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3545 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3554 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h52789 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step94895 (p2383 p2437 p2668 p2962 p3324 p4109 p4194 p4646 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h41194 : (¬ p2383) ∨ (¬ p2437) ∨ (¬ p2962) ∨ (¬ p3324) ∨ (¬ p4109) ∨ (¬ p4194) ∨ (¬ p4646))
    : (¬ p2383) ∨ (¬ p4194) ∨ (¬ p4646) ∨ (¬ p4109) ∨ (¬ p2962) ∨ (¬ p2437) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h41194 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step94897 (p2352 p2573 p2665 p2668 p3324 p4194 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h59986 : (¬ p2352) ∨ (¬ p2573) ∨ (¬ p2665) ∨ (¬ p3324) ∨ (¬ p4194))
    : (¬ p2352) ∨ (¬ p2573) ∨ (¬ p2665) ∨ p2668 ∨ (¬ p4194) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h59986 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step94900 (p2470 p2528 p2665 p3256 p4118 p4194 p4196 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h48460 : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2665) ∨ (¬ p4118) ∨ (¬ p4194) ∨ (¬ p4196))
    : (¬ p2470) ∨ (¬ p4194) ∨ (¬ p2528) ∨ (¬ p2665) ∨ (¬ p4196) ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4196 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h48460 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step94902 (p2295 p2440 p2542 p2553 p3568 p4194 p4715 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73270 : p2542 ∨ p2440)
    (h50272 : (¬ p2542) ∨ (¬ p2553) ∨ (¬ p3568) ∨ (¬ p4194) ∨ (¬ p4715))
    : p2295 ∨ p2440 ∨ (¬ p4194) ∨ (¬ p4715) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2295) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h50272 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step94903 (p2177 p2264 p2307 p3553 p4067 p4584 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h49537 : (¬ p2177) ∨ (¬ p2307) ∨ (¬ p3553) ∨ (¬ p4067) ∨ (¬ p4584))
    : (¬ p2177) ∨ (¬ p2307) ∨ (¬ p4067) ∨ p2264 ∨ (¬ p4584) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49537 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step94907 (p2737 p2829 p3688 p4426 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h26310 : (¬ p2737) ∨ (¬ p3688) ∨ (¬ p4426))
    : (¬ p4426) ∨ p2829 ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4426 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h26310 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u0)))))))

theorem step94909 (p2383 p2387 p2630 p2667 p2810 p2819 p4426 p4975 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h73316 : p2810 ∨ p2630)
    (h50655 : (¬ p2387) ∨ (¬ p2667) ∨ (¬ p2810) ∨ (¬ p2819) ∨ (¬ p4426) ∨ (¬ p4975))
    : (¬ p2819) ∨ p2383 ∨ (¬ p4426) ∨ (¬ p4975) ∨ p2630 ∨ (¬ p2667) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2383) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50655 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step94912 (p2383 p2387 p2577 p2662 p2819 p3136 p4315 p4426 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h73550 : p4315 ∨ p3136)
    (h69689 : (¬ p2819) ∨ (¬ p2387) ∨ (¬ p2662) ∨ (¬ p2577) ∨ (¬ p4426) ∨ (¬ p4315))
    : p2383 ∨ (¬ p2819) ∨ (¬ p2577) ∨ p3136 ∨ (¬ p2662) ∨ (¬ p4426) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2383) := (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69689 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step94914 (p2668 p2737 p3323 p3483 p4037 p4426 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h44536 : (¬ p2668) ∨ (¬ p2737) ∨ (¬ p3483) ∨ (¬ p4037) ∨ (¬ p4426))
    : p3323 ∨ (¬ p3483) ∨ (¬ p2668) ∨ (¬ p2737) ∨ (¬ p4426) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h44536 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step94915 (p2352 p2630 p2651 p2810 p2819 p3956 p4117 p4426 : Prop)
    (h73500 : p3956 ∨ p2352)
    (h73316 : p2810 ∨ p2630)
    (h55623 : (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2819) ∨ (¬ p3956) ∨ (¬ p4117) ∨ (¬ p4426))
    : (¬ p2819) ∨ (¬ p4426) ∨ (¬ p4117) ∨ p2352 ∨ p2630 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55623 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step94916 (p2122 p2295 p2641 p2745 p3568 p4154 p4426 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73526 : p4154 ∨ p2641)
    (h48018 : (¬ p2122) ∨ (¬ p2745) ∨ (¬ p3568) ∨ (¬ p4154) ∨ (¬ p4426))
    : p2295 ∨ p2641 ∨ (¬ p2122) ∨ (¬ p4426) ∨ (¬ p2745) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2295) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h48018 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step94926 (p2177 p2299 p2396 p3256 p4118 p4443 p4550 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h73234 : p2299 ∨ p2177)
    (h50147 : (¬ p2299) ∨ (¬ p2396) ∨ (¬ p4118) ∨ (¬ p4443) ∨ (¬ p4550))
    : (¬ p2396) ∨ p3256 ∨ p2177 ∨ (¬ p4443) ∨ (¬ p4550) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4443 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50147 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step94935 (p2230 p2427 p2589 p2696 p2753 p2881 p3256 p3347 p3570 p3609 p4118 p4235 p4373 p4550 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73418 : p3570 ∨ p2881)
    (h73284 : p2589 ∨ p2230)
    (h73520 : p4118 ∨ p3256)
    (h72077 : (¬ p4373) ∨ (¬ p3347) ∨ (¬ p3570) ∨ (¬ p4550) ∨ (¬ p2589) ∨ (¬ p3609) ∨ (¬ p2696) ∨ (¬ p4235) ∨ (¬ p2753) ∨ (¬ p4118))
    : (¬ p2753) ∨ (¬ p3609) ∨ (¬ p4550) ∨ p2427 ∨ (¬ p4373) ∨ (¬ p2696) ∨ p2881 ∨ (¬ p3347) ∨ p2230 ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2753 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u13 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h72077 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (False.elim (r8 u13)))))))))))))))))))))

theorem step94936 (p2166 p2191 p2210 p2248 p2331 p2797 p3146 p3555 p3692 p3755 p4195 p5109 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73222 : p2191 ∨ p2166)
    (h73412 : p3555 ∨ p2210)
    (h73448 : p3692 ∨ p3146)
    (h57980 : (¬ p2191) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p3555) ∨ (¬ p3692) ∨ (¬ p3755) ∨ (¬ p4195) ∨ (¬ p5109))
    : (¬ p3755) ∨ p2797 ∨ (¬ p5109) ∨ p2166 ∨ p2210 ∨ (¬ p2331) ∨ p3146 ∨ (¬ p2248) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2191 := (Or.elim h73222 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h57980 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step94937 (p2248 p2331 p2509 p2528 p2534 p2797 p3379 p3452 p3755 p4195 p5109 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73268 : p2534 ∨ p2528)
    (h73394 : p3452 ∨ p3379)
    (h64460 : (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p3452) ∨ (¬ p3755) ∨ (¬ p4195) ∨ (¬ p5109))
    : (¬ p3755) ∨ p2797 ∨ (¬ p5109) ∨ p2528 ∨ (¬ p2248) ∨ (¬ p2509) ∨ p3379 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h64460 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step94942 (p3005 p3266 p3506 p3755 p3877 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73488 : p3877 ∨ p3005)
    (h49085 : (¬ p3506) ∨ (¬ p3755) ∨ (¬ p3877) ∨ (¬ p4444))
    : (¬ p3755) ∨ (¬ p3506) ∨ p3266 ∨ p3005 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49085 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step94943 (p3005 p3755 p3877 p4349 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h20723 : (¬ p3755) ∨ (¬ p3877) ∨ (¬ p4349))
    : (¬ p3755) ∨ (¬ p4349) ∨ p3005 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4349 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20723 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step94949 (p2246 p2352 p2363 p2573 p2579 p2749 p2946 p3136 p3347 p3755 p3956 p4039 p4315 p4347 p4450 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73500 : p3956 ∨ p2352)
    (h73274 : p2579 ∨ p2573)
    (h73550 : p4315 ∨ p3136)
    (h72078 : (¬ p3347) ∨ (¬ p4450) ∨ (¬ p2246) ∨ (¬ p3956) ∨ (¬ p3755) ∨ (¬ p2579) ∨ (¬ p2749) ∨ (¬ p4315) ∨ (¬ p2946) ∨ (¬ p4347) ∨ (¬ p4039))
    : (¬ p4039) ∨ p2363 ∨ (¬ p2749) ∨ (¬ p3755) ∨ (¬ p2246) ∨ (¬ p4450) ∨ (¬ p2946) ∨ p2352 ∨ p2573 ∨ (¬ p3347) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4039 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u13 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u14 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h72078 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u14))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u11))) (fun r9 => (False.elim (r9 u0)))))))))))))))))))))))

theorem step94954 (p2797 p3125 p3291 p3744 p3755 p4038 p4195 p4560 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h72955 : p4560)
    (h73454 : p3744 ∨ p3125)
    (h51145 : (¬ p3291) ∨ (¬ p3744) ∨ (¬ p3755) ∨ (¬ p4038) ∨ (¬ p4195) ∨ (¬ p4560))
    : (¬ p3755) ∨ p2797 ∨ (¬ p3291) ∨ p3125 ∨ (¬ p4038) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3291 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4038 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4560 := h72955;
    let u7 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h51145 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step94955 (p2797 p3755 p4195 p5274 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h20725 : (¬ p3755) ∨ (¬ p4195) ∨ (¬ p5274))
    : (¬ p3755) ∨ p2797 ∨ (¬ p5274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h20725 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step94956 (p2331 p2797 p3461 p3755 p4195 p4367 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h48975 : (¬ p2331) ∨ (¬ p3461) ∨ (¬ p3755) ∨ (¬ p4195) ∨ (¬ p4367))
    : (¬ p3755) ∨ p2797 ∨ (¬ p3461) ∨ (¬ p4367) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h48975 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step94957 (p2630 p2810 p3083 p3755 p3848 p4256 : Prop)
    (h73542 : p4256 ∨ p3083)
    (h73316 : p2810 ∨ p2630)
    (h44865 : (¬ p2810) ∨ (¬ p3755) ∨ (¬ p3848) ∨ (¬ p4256))
    : (¬ p3755) ∨ p3083 ∨ (¬ p3848) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3848 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44865 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step94958 (p2331 p2459 p2753 p2797 p2911 p3347 p3389 p3540 p3644 p3755 p4117 p4195 p4330 p4348 p4367 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73402 : p3540 ∨ p3389)
    (h73562 : p4348 ∨ p2459)
    (h73532 : p4195 ∨ p2797)
    (h72079 : (¬ p3755) ∨ (¬ p4367) ∨ (¬ p2331) ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p4330) ∨ (¬ p3644) ∨ (¬ p2753) ∨ (¬ p4117) ∨ (¬ p4348) ∨ (¬ p4195))
    : p2911 ∨ (¬ p2753) ∨ (¬ p2331) ∨ (¬ p3347) ∨ (¬ p3755) ∨ (¬ p4330) ∨ (¬ p4117) ∨ (¬ p4367) ∨ p3389 ∨ p2459 ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u13 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u14 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h72079 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u13))) (fun r9 => (False.elim (r9 u14)))))))))))))))))))))))

theorem step94959 (p2630 p2810 p3755 p5170 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h20459 : (¬ p2810) ∨ (¬ p3755) ∨ (¬ p5170))
    : (¬ p3755) ∨ (¬ p5170) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20459 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step94965 (p2630 p2651 p2810 p3506 p3755 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h45097 : (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3506) ∨ (¬ p3755))
    : (¬ p3506) ∨ (¬ p3755) ∨ (¬ p2651) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45097 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step94966 (p2608 p2630 p2810 p3755 p3830 p3834 p3847 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h73316 : p2810 ∨ p2630)
    (h47850 : (¬ p2608) ∨ (¬ p2810) ∨ (¬ p3755) ∨ (¬ p3834) ∨ (¬ p3847))
    : p3830 ∨ (¬ p3755) ∨ (¬ p3847) ∨ p2630 ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3847 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47850 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step94970 (p2295 p2797 p3568 p3755 p4195 p4367 p4624 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73416 : p3568 ∨ p2295)
    (h50895 : (¬ p3568) ∨ (¬ p3755) ∨ (¬ p4195) ∨ (¬ p4367) ∨ (¬ p4624))
    : (¬ p3755) ∨ p2797 ∨ p2295 ∨ (¬ p4367) ∨ (¬ p4624) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4624 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50895 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step94973 (p2685 p2807 p3506 p3572 p3755 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h53470 : (¬ p2807) ∨ (¬ p3506) ∨ (¬ p3572) ∨ (¬ p3755))
    : (¬ p3755) ∨ (¬ p3506) ∨ p2685 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h53470 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step94974 (p2241 p2641 p2797 p3755 p4195 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h47657 : (¬ p2241) ∨ (¬ p2641) ∨ (¬ p3755) ∨ (¬ p4195))
    : (¬ p3755) ∨ (¬ p2641) ∨ (¬ p2241) ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47657 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step94977 (p2651 p3136 p3286 p3292 p3755 p4315 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h73550 : p4315 ∨ p3136)
    (h69691 : (¬ p3755) ∨ (¬ p3292) ∨ (¬ p2651) ∨ (¬ p4315))
    : (¬ p3755) ∨ p3286 ∨ p3136 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h69691 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step94978 (p2274 p2307 p2313 p2630 p2651 p2787 p2810 p3125 p3744 p3755 p4117 p5276 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h73316 : p2810 ∨ p2630)
    (h73238 : p2313 ∨ p2307)
    (h62758 : (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2651) ∨ (¬ p2787) ∨ (¬ p2810) ∨ (¬ p3744) ∨ (¬ p3755) ∨ (¬ p4117) ∨ (¬ p5276))
    : (¬ p3755) ∨ (¬ p5276) ∨ p3125 ∨ p2630 ∨ (¬ p2651) ∨ (¬ p4117) ∨ p2307 ∨ (¬ p2787) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h62758 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step94981 (p2363 p3005 p3755 p3877 p4347 p4350 p4774 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73560 : p4347 ∨ p2363)
    (h63528 : (¬ p3755) ∨ (¬ p3877) ∨ (¬ p4347) ∨ (¬ p4350) ∨ (¬ p4774))
    : (¬ p3755) ∨ (¬ p4350) ∨ p3005 ∨ (¬ p4774) ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4350 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63528 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step94982 (p2459 p3005 p3291 p3755 p3877 p4348 p4437 p4438 p4460 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73562 : p4348 ∨ p2459)
    (h63527 : (¬ p3291) ∨ (¬ p3755) ∨ (¬ p3877) ∨ (¬ p4348) ∨ (¬ p4437) ∨ (¬ p4438) ∨ (¬ p4460))
    : (¬ p3755) ∨ (¬ p3291) ∨ (¬ p4460) ∨ p3005 ∨ (¬ p4438) ∨ p2459 ∨ (¬ p4437) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3291 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4460 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h63527 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step94986 (p2230 p2331 p2373 p2589 p2797 p3146 p3692 p3755 p3880 p4117 p4195 p4729 p5109 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73284 : p2589 ∨ p2230)
    (h73448 : p3692 ∨ p3146)
    (h73490 : p3880 ∨ p2373)
    (h56675 : (¬ p2331) ∨ (¬ p2589) ∨ (¬ p3692) ∨ (¬ p3755) ∨ (¬ p3880) ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p4729) ∨ (¬ p5109))
    : (¬ p3755) ∨ p2797 ∨ p2230 ∨ (¬ p4729) ∨ p3146 ∨ (¬ p5109) ∨ (¬ p2331) ∨ (¬ p4117) ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h56675 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step94987 (p2737 p3266 p3506 p3755 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h44107 : (¬ p2737) ∨ (¬ p3506) ∨ (¬ p3755) ∨ (¬ p4444))
    : (¬ p3506) ∨ p3266 ∨ (¬ p2737) ∨ (¬ p3755) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h44107 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step94989 (p2630 p2761 p2810 p3506 p3755 p4381 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73574 : p4381 ∨ p2761)
    (h62628 : (¬ p2810) ∨ (¬ p3506) ∨ (¬ p3755) ∨ (¬ p4381))
    : (¬ p3755) ∨ (¬ p3506) ∨ p2630 ∨ p2761 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62628 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step94992 (p3136 p3755 p4314 p4315 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h6536 : (¬ p3755) ∨ (¬ p4314) ∨ (¬ p4315))
    : (¬ p3755) ∨ (¬ p4314) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4314 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h6536 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step94993 (p2156 p2246 p2274 p2396 p2630 p2651 p2749 p2810 p3097 p3645 p3646 p3755 p4107 p4638 p4877 p5175 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73514 : p4107 ∨ p2396)
    (h73436 : p3646 ∨ p2156)
    (h73352 : p3097 ∨ p2274)
    (h53816 : (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2749) ∨ (¬ p2810) ∨ (¬ p3097) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3755) ∨ (¬ p4107) ∨ (¬ p4638) ∨ (¬ p4877) ∨ (¬ p5175))
    : (¬ p5175) ∨ (¬ p2246) ∨ p2630 ∨ (¬ p2749) ∨ (¬ p4877) ∨ p2396 ∨ (¬ p2651) ∨ (¬ p3645) ∨ (¬ p3755) ∨ p2156 ∨ p2274 ∨ (¬ p4638) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5175 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4638 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u13 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u14 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u15 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h53816 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u15))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u14))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u13))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u11))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u4))) (fun r10 => (False.elim (r10 u0)))))))))))))))))))))))))

theorem step95000 (p2230 p2373 p2589 p2696 p3506 p3755 p3880 p4729 p5123 p5568 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73284 : p2589 ∨ p2230)
    (h51346 : (¬ p2589) ∨ (¬ p2696) ∨ (¬ p3506) ∨ (¬ p3755) ∨ (¬ p3880) ∨ (¬ p4729) ∨ (¬ p5123) ∨ (¬ p5568))
    : (¬ p5568) ∨ (¬ p3506) ∨ (¬ p3755) ∨ (¬ p5123) ∨ (¬ p2696) ∨ p2373 ∨ p2230 ∨ (¬ p4729) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5568 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u9 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h51346 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step95005 (p3005 p3146 p3692 p3755 p3877 p4043 p4350 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73448 : p3692 ∨ p3146)
    (h57232 : (¬ p3692) ∨ (¬ p3755) ∨ (¬ p3877) ∨ (¬ p4043) ∨ (¬ p4350))
    : p3005 ∨ (¬ p3755) ∨ p3146 ∨ (¬ p4350) ∨ (¬ p4043) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4350 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h57232 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step95011 (p2553 p2573 p2579 p2588 p2696 p3506 p3589 p3755 p4260 p4831 p5193 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73282 : p2588 ∨ p2553)
    (h63953 : (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2696) ∨ (¬ p3506) ∨ (¬ p3589) ∨ (¬ p3755) ∨ (¬ p4260) ∨ (¬ p4831) ∨ (¬ p5193))
    : (¬ p3506) ∨ (¬ p4260) ∨ p2573 ∨ (¬ p5193) ∨ (¬ p3589) ∨ (¬ p3755) ∨ p2553 ∨ (¬ p2696) ∨ (¬ p4831) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h63953 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step95016 (p2528 p2534 p3005 p3755 p3877 p4350 p5012 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73268 : p2534 ∨ p2528)
    (h57544 : (¬ p2534) ∨ (¬ p3755) ∨ (¬ p3877) ∨ (¬ p4350) ∨ (¬ p5012))
    : p3005 ∨ (¬ p3755) ∨ p2528 ∨ (¬ p4350) ∨ (¬ p5012) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4350 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5012 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h57544 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step95018 (p2145 p2156 p2553 p2588 p2696 p3506 p3646 p3755 p4203 p4260 p4831 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73282 : p2588 ∨ p2553)
    (h58590 : (¬ p2145) ∨ (¬ p2588) ∨ (¬ p2696) ∨ (¬ p3506) ∨ (¬ p3646) ∨ (¬ p3755) ∨ (¬ p4203) ∨ (¬ p4260) ∨ (¬ p4831))
    : (¬ p4260) ∨ (¬ p3506) ∨ p2156 ∨ (¬ p2145) ∨ (¬ p4831) ∨ (¬ p2696) ∨ (¬ p4203) ∨ p2553 ∨ (¬ p3755) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4260 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h58590 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step95019 (p2284 p2459 p2911 p3136 p3286 p3292 p3389 p3755 p3952 p4236 p4315 p4419 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73496 : p3952 ∨ p2284)
    (h73378 : p3292 ∨ p3286)
    (h58772 : (¬ p2459) ∨ (¬ p2911) ∨ (¬ p3292) ∨ (¬ p3389) ∨ (¬ p3755) ∨ (¬ p3952) ∨ (¬ p4236) ∨ (¬ p4315) ∨ (¬ p4419))
    : (¬ p3389) ∨ p3136 ∨ (¬ p2911) ∨ (¬ p2459) ∨ (¬ p4236) ∨ (¬ p4419) ∨ p2284 ∨ (¬ p3755) ∨ p3286 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3136) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h58772 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step95023 (p2493 p3136 p3193 p3755 p4315 p5175 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h63514 : (¬ p2493) ∨ (¬ p3193) ∨ (¬ p3755) ∨ (¬ p4315) ∨ (¬ p5175))
    : (¬ p3755) ∨ (¬ p3193) ∨ (¬ p5175) ∨ p3136 ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5175 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63514 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step95024 (p2230 p2427 p2589 p2608 p2737 p3246 p3690 p3755 p4235 p4658 p5193 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73284 : p2589 ∨ p2230)
    (h73536 : p4235 ∨ p2427)
    (h55732 : (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2737) ∨ (¬ p3690) ∨ (¬ p3755) ∨ (¬ p4235) ∨ (¬ p4658) ∨ (¬ p5193))
    : (¬ p3755) ∨ (¬ p2608) ∨ (¬ p4658) ∨ p3246 ∨ (¬ p2737) ∨ p2230 ∨ p2427 ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4658 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h55732 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step95026 (p2797 p3654 p3755 p3946 p4195 p4367 p4581 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73492 : p3946 ∨ p3654)
    (h57772 : (¬ p3755) ∨ (¬ p3946) ∨ (¬ p4195) ∨ (¬ p4367) ∨ (¬ p4581))
    : (¬ p3755) ∨ p2797 ∨ (¬ p4367) ∨ (¬ p4581) ∨ p3654 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h57772 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step95032 (p3136 p3506 p3755 p4315 p4322 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h56206 : (¬ p3506) ∨ (¬ p3755) ∨ (¬ p4315) ∨ (¬ p4322))
    : (¬ p4322) ∨ (¬ p3506) ∨ (¬ p3755) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56206 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step95034 (p2696 p3461 p3506 p3755 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h46049 : (¬ p2696) ∨ (¬ p3506) ∨ (¬ p3755) ∨ (¬ p4191))
    : (¬ p3506) ∨ p3461 ∨ (¬ p3755) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46049 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step95035 (p2630 p2810 p3461 p3506 p3755 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73316 : p2810 ∨ p2630)
    (h55220 : (¬ p2810) ∨ (¬ p3506) ∨ (¬ p3755) ∨ (¬ p4191))
    : (¬ p3506) ∨ p3461 ∨ (¬ p3755) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55220 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step95040 (p2230 p2373 p2589 p2685 p2807 p3146 p3572 p3692 p3755 p3880 p4117 p4729 p5109 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73420 : p3572 ∨ p2685)
    (h73284 : p2589 ∨ p2230)
    (h73490 : p3880 ∨ p2373)
    (h55955 : (¬ p2589) ∨ (¬ p2807) ∨ (¬ p3572) ∨ (¬ p3692) ∨ (¬ p3755) ∨ (¬ p3880) ∨ (¬ p4117) ∨ (¬ p4729) ∨ (¬ p5109))
    : (¬ p5109) ∨ p3146 ∨ p2685 ∨ (¬ p2807) ∨ p2230 ∨ p2373 ∨ (¬ p4117) ∨ (¬ p3755) ∨ (¬ p4729) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5109 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h55955 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step95041 (p2230 p2563 p2589 p2685 p2807 p3125 p3572 p3744 p3755 p4110 p4117 p4729 p5276 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h73516 : p4110 ∨ p2563)
    (h73454 : p3744 ∨ p3125)
    (h73284 : p2589 ∨ p2230)
    (h57519 : (¬ p2589) ∨ (¬ p2807) ∨ (¬ p3572) ∨ (¬ p3744) ∨ (¬ p3755) ∨ (¬ p4110) ∨ (¬ p4117) ∨ (¬ p4729) ∨ (¬ p5276))
    : (¬ p3755) ∨ (¬ p5276) ∨ (¬ p2807) ∨ (¬ p4729) ∨ p2685 ∨ p2563 ∨ (¬ p4117) ∨ p3125 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h57519 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step95047 (p2246 p2352 p2363 p2573 p2579 p2685 p2749 p2807 p3347 p3572 p3755 p3956 p4347 p5109 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73500 : p3956 ∨ p2352)
    (h73274 : p2579 ∨ p2573)
    (h73420 : p3572 ∨ p2685)
    (h72087 : (¬ p3755) ∨ (¬ p3347) ∨ (¬ p3956) ∨ (¬ p2246) ∨ (¬ p2807) ∨ (¬ p2579) ∨ (¬ p3572) ∨ (¬ p4347) ∨ (¬ p5109) ∨ (¬ p2749))
    : (¬ p3755) ∨ p2363 ∨ p2352 ∨ (¬ p2246) ∨ (¬ p2807) ∨ (¬ p3347) ∨ p2573 ∨ p2685 ∨ (¬ p5109) ∨ (¬ p2749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h72087 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step95048 (p2284 p2352 p2363 p2573 p3136 p3286 p3292 p3755 p3952 p4236 p4315 p4419 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73378 : p3292 ∨ p3286)
    (h73496 : p3952 ∨ p2284)
    (h46965 : (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p3292) ∨ (¬ p3755) ∨ (¬ p3952) ∨ (¬ p4236) ∨ (¬ p4315) ∨ (¬ p4419))
    : (¬ p3755) ∨ p3136 ∨ p3286 ∨ (¬ p2363) ∨ (¬ p2352) ∨ p2284 ∨ (¬ p4236) ∨ (¬ p2573) ∨ (¬ p4419) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3136) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h46965 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step95049 (p2307 p2352 p2553 p2588 p3005 p3286 p3292 p3366 p3755 p3877 p4236 p4774 p4866 p5016 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h73488 : p3877 ∨ p3005)
    (h73282 : p2588 ∨ p2553)
    (h64621 : (¬ p2307) ∨ (¬ p2352) ∨ (¬ p2588) ∨ (¬ p3292) ∨ (¬ p3366) ∨ (¬ p3755) ∨ (¬ p3877) ∨ (¬ p4236) ∨ (¬ p4774) ∨ (¬ p4866) ∨ (¬ p5016))
    : (¬ p3755) ∨ (¬ p5016) ∨ (¬ p4866) ∨ p3286 ∨ p3005 ∨ p2553 ∨ (¬ p2352) ∨ (¬ p4774) ∨ (¬ p2307) ∨ (¬ p3366) ∨ (¬ p4236) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4866 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u13 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h64621 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u13))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (False.elim (r9 u1)))))))))))))))))))))))

theorem step95054 (p2630 p2651 p2753 p2810 p3204 p3266 p3461 p3654 p3755 p3946 p4117 p4191 p4512 p4877 p5109 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73316 : p2810 ∨ p2630)
    (h73492 : p3946 ∨ p3654)
    (h50804 : (¬ p2651) ∨ (¬ p2753) ∨ (¬ p2810) ∨ (¬ p3204) ∨ (¬ p3266) ∨ (¬ p3755) ∨ (¬ p3946) ∨ (¬ p4117) ∨ (¬ p4191) ∨ (¬ p4512) ∨ (¬ p4877) ∨ (¬ p5109))
    : (¬ p3266) ∨ (¬ p4512) ∨ p3461 ∨ (¬ p5109) ∨ (¬ p2753) ∨ (¬ p4877) ∨ (¬ p3755) ∨ p2630 ∨ (¬ p2651) ∨ (¬ p3204) ∨ (¬ p4117) ∨ p3654 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u13 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u14 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    (Or.elim h50804 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u13))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u14))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u1))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u5))) (fun r10 => (False.elim (r10 u3)))))))))))))))))))))))))

theorem step95061 (p3166 p3286 p3292 p5111 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h19949 : (¬ p3166) ∨ (¬ p3292) ∨ (¬ p5111))
    : p3286 ∨ (¬ p5111) ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3286) := (fun h => hn (Or.inl h));
    let u1 : p5111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h19949 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step95064 (p2528 p2534 p3266 p3707 p4351 p4444 p4690 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73268 : p2534 ∨ p2528)
    (h48665 : (¬ p2534) ∨ (¬ p3707) ∨ (¬ p4351) ∨ (¬ p4444) ∨ (¬ p4690))
    : p3266 ∨ (¬ p3707) ∨ p2528 ∨ (¬ p4690) ∨ (¬ p4351) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4351 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48665 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step95068 (p3256 p4118 p4351 p4352 p5074 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h14152 : (¬ p4118) ∨ (¬ p4351) ∨ (¬ p4352) ∨ (¬ p5074))
    : (¬ p5074) ∨ p3256 ∨ (¬ p4351) ∨ (¬ p4352) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5074 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4351 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h14152 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step95070 (p2241 p2247 p3830 p3846 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h6482 : (¬ p2247) ∨ (¬ p3830) ∨ (¬ p3846))
    : (¬ p3846) ∨ (¬ p3830) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3846 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h6482 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step95072 (p2241 p2247 p3399 p3846 p5363 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h22801 : (¬ p2247) ∨ (¬ p3399) ∨ (¬ p3846) ∨ (¬ p5363))
    : (¬ p3846) ∨ (¬ p3399) ∨ p2241 ∨ (¬ p5363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3846 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h22801 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step95078 (p2373 p3880 p3998 p4238 p4539 p5568 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h50111 : (¬ p3880) ∨ (¬ p3998) ∨ (¬ p4238) ∨ (¬ p4539) ∨ (¬ p5568))
    : (¬ p3998) ∨ (¬ p5568) ∨ p2373 ∨ (¬ p4238) ∨ (¬ p4539) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3998 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4539 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50111 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step95080 (p2881 p4132 p4900 : Prop)
    (h73818 : p4900 ∨ p2881)
    (h8085 : p4132 ∨ (¬ p4900))
    : p4132 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4132) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr h));
    let u2 : p4900 := (Or.elim h73818 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h8085 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step95081 (p2881 p4132 p5941 : Prop)
    (h74261 : p2881 ∨ (¬ p5941))
    (h12630 : p4132 ∨ p5941)
    : p4132 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4132) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5941) := (Or.elim h74261 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12630 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95086 (p2145 p2598 p2881 p3051 p3276 p3333 p3556 p3570 p5123 p5558 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73418 : p3570 ∨ p2881)
    (h58380 : (¬ p2145) ∨ (¬ p2598) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p5123) ∨ (¬ p5558))
    : (¬ p5558) ∨ (¬ p3333) ∨ (¬ p2145) ∨ p3051 ∨ (¬ p2598) ∨ p2881 ∨ (¬ p3276) ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5558 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h58380 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step95087 (p2145 p2264 p2459 p3051 p3276 p3355 p3362 p3461 p3553 p3556 p4191 p4330 p4333 p4348 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73410 : p3553 ∨ p2264)
    (h73414 : p3556 ∨ p3051)
    (h73562 : p4348 ∨ p2459)
    (h64998 : (¬ p2145) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3362) ∨ (¬ p3553) ∨ (¬ p3556) ∨ (¬ p4191) ∨ (¬ p4330) ∨ (¬ p4333) ∨ (¬ p4348))
    : (¬ p3276) ∨ p3461 ∨ p2264 ∨ (¬ p3362) ∨ (¬ p2145) ∨ (¬ p4330) ∨ p3051 ∨ (¬ p3355) ∨ p2459 ∨ (¬ p4333) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h64998 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u13)))))))))))))))))))))

theorem step95093 (p2230 p2341 p2406 p2881 p3238 p3551 p4257 p5197 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73374 : p3238 ∨ p2406)
    (h63645 : (¬ p2230) ∨ (¬ p2881) ∨ (¬ p3238) ∨ (¬ p3551) ∨ (¬ p4257) ∨ (¬ p5197))
    : p2341 ∨ (¬ p4257) ∨ p2406 ∨ (¬ p2230) ∨ (¬ p5197) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h63645 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step95094 (p2210 p2241 p2247 p2341 p2563 p2744 p2891 p2911 p3347 p3551 p3741 p4110 p4257 p4558 p5197 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73408 : p3551 ∨ p2341)
    (h73516 : p4110 ∨ p2563)
    (h54398 : (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p2891) ∨ (¬ p2911) ∨ (¬ p3347) ∨ (¬ p3551) ∨ (¬ p3741) ∨ (¬ p4110) ∨ (¬ p4257) ∨ (¬ p4558) ∨ (¬ p5197))
    : p2241 ∨ (¬ p5197) ∨ (¬ p3347) ∨ (¬ p2891) ∨ p2341 ∨ (¬ p4257) ∨ (¬ p3741) ∨ (¬ p2744) ∨ (¬ p2911) ∨ (¬ p2210) ∨ p2563 ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u13 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u14 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h54398 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u14))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u5))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u11))) (fun r10 => (False.elim (r10 u1)))))))))))))))))))))))))

theorem step95097 (p2341 p2573 p2911 p3551 p3741 p4717 p5197 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h53263 : (¬ p2573) ∨ (¬ p2911) ∨ (¬ p3551) ∨ (¬ p3741) ∨ (¬ p4717) ∨ (¬ p5197))
    : (¬ p2911) ∨ p2341 ∨ (¬ p2573) ∨ (¬ p3741) ∨ (¬ p4717) ∨ (¬ p5197) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h53263 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step95101 (p2341 p2573 p2911 p3551 p4708 p5197 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h48065 : (¬ p2573) ∨ (¬ p2911) ∨ (¬ p3551) ∨ (¬ p4708) ∨ (¬ p5197))
    : (¬ p2911) ∨ p2341 ∨ (¬ p4708) ∨ (¬ p2573) ∨ (¬ p5197) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4708 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h48065 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step95120 (p2136 p2137 p2737 p2774 p2829 p3688 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h67285 : (¬ p2136) ∨ (¬ p2737) ∨ (¬ p2137) ∨ (¬ p2774) ∨ (¬ p3688))
    : (¬ p2137) ∨ (¬ p2136) ∨ p2829 ∨ (¬ p2737) ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2137 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h67285 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step95121 (p2136 p2220 p2573 p3016 p3266 p3343 p3366 p3519 p3574 p4120 p4322 p4332 p4335 p4376 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h73422 : p3574 ∨ p3016)
    (h56744 : (¬ p2136) ∨ (¬ p2573) ∨ (¬ p3266) ∨ (¬ p3343) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3574) ∨ (¬ p4120) ∨ (¬ p4322) ∨ (¬ p4332) ∨ (¬ p4335) ∨ (¬ p4376))
    : (¬ p4322) ∨ (¬ p3266) ∨ (¬ p4376) ∨ (¬ p4332) ∨ (¬ p2573) ∨ p2220 ∨ (¬ p4335) ∨ (¬ p3343) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p2136) ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4335 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    (Or.elim h56744 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u3))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u6))) (fun r10 => (False.elim (r10 u2)))))))))))))))))))))))))

theorem step95123 (p2136 p2156 p2187 p2363 p2761 p3286 p3506 p3646 p3950 p3989 p4347 p4381 p4786 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73560 : p4347 ∨ p2363)
    (h73502 : p3989 ∨ p2187)
    (h73574 : p4381 ∨ p2761)
    (h56255 : (¬ p2136) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p3646) ∨ (¬ p3950) ∨ (¬ p3989) ∨ (¬ p4347) ∨ (¬ p4381) ∨ (¬ p4786))
    : (¬ p3286) ∨ (¬ p3506) ∨ (¬ p3950) ∨ p2156 ∨ p2363 ∨ p2187 ∨ p2761 ∨ (¬ p2136) ∨ (¬ p4786) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3286 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h56255 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step95124 (p2136 p2156 p2246 p2363 p2437 p2663 p2744 p3083 p3146 p3366 p3389 p3646 p3692 p3742 p3988 p4596 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73448 : p3692 ∨ p3146)
    (h73436 : p3646 ∨ p2156)
    (h52961 : (¬ p2136) ∨ (¬ p2246) ∨ (¬ p2363) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3366) ∨ (¬ p3389) ∨ (¬ p3646) ∨ (¬ p3692) ∨ (¬ p3742) ∨ (¬ p3988) ∨ (¬ p4596))
    : (¬ p3389) ∨ p2437 ∨ (¬ p2363) ∨ p3146 ∨ (¬ p3083) ∨ p2156 ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p4596) ∨ (¬ p2246) ∨ (¬ p2663) ∨ (¬ p3988) ∨ (¬ p2136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u14 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u15 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h52961 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u15))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u14))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u13))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u11))) (fun r11 => (False.elim (r11 u8)))))))))))))))))))))))))))

theorem step95135 (p2136 p2220 p2598 p2619 p4120 p4313 p4752 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h51776 : (¬ p2136) ∨ (¬ p2598) ∨ (¬ p2619) ∨ (¬ p4120) ∨ (¬ p4313) ∨ (¬ p4752))
    : (¬ p2136) ∨ (¬ p4313) ∨ p2220 ∨ (¬ p4752) ∨ (¬ p2598) ∨ (¬ p2619) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h51776 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step95140 (p2807 p3323 p3414 p3654 p3987 p4037 p4194 p4650 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73392 : p3414 ∨ p2807)
    (h41608 : (¬ p3414) ∨ (¬ p3654) ∨ (¬ p3987) ∨ (¬ p4037) ∨ (¬ p4194) ∨ (¬ p4650))
    : (¬ p3654) ∨ p3323 ∨ (¬ p4650) ∨ p2807 ∨ (¬ p4194) ∨ (¬ p3987) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41608 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step95141 (p2230 p2440 p2663 p2807 p3414 p4650 : Prop)
    (h73392 : p3414 ∨ p2807)
    (h53710 : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p3414) ∨ (¬ p4650))
    : (¬ p2230) ∨ p2807 ∨ (¬ p4650) ∨ (¬ p2663) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2807) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h53710 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step95142 (p2449 p3389 p3516 p3540 p3947 p4327 p5201 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73402 : p3540 ∨ p3389)
    (h56407 : (¬ p3516) ∨ (¬ p3540) ∨ (¬ p3947) ∨ (¬ p4327) ∨ (¬ p5201))
    : (¬ p3516) ∨ p2449 ∨ (¬ p4327) ∨ p3389 ∨ (¬ p5201) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4327 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56407 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step95143 (p2807 p2911 p3166 p3172 p4327 p4548 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h41491 : (¬ p2807) ∨ (¬ p2911) ∨ (¬ p3172) ∨ (¬ p4327) ∨ (¬ p4548))
    : p3166 ∨ (¬ p2911) ∨ (¬ p4327) ∨ (¬ p2807) ∨ (¬ p4548) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4327 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41491 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step95145 (p3767 p3777 p3782 : Prop)
    (h73459 : (¬ p3777) ∨ (¬ p3782))
    (h5554 : p3767 ∨ p3782)
    : p3767 ∨ (¬ p3777) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3767) := (fun h => hn (Or.inl h));
    let u1 : p3777 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3782) := (Or.elim h73459 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h5554 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95146 (p2230 p2440 p2663 p3286 p3292 p5172 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h62134 : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p3292) ∨ (¬ p5172))
    : (¬ p2230) ∨ p3286 ∨ (¬ p2663) ∨ (¬ p5172) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h62134 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step95149 (p2850 p3276 p3333 p3684 p3773 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h43277 : (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3684) ∨ (¬ p3773))
    : (¬ p3773) ∨ (¬ p3333) ∨ (¬ p3276) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3773 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43277 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step95161 (p2156 p2177 p2241 p2274 p2299 p2727 p3083 p3097 p3646 p4420 p4524 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73436 : p3646 ∨ p2156)
    (h73234 : p2299 ∨ p2177)
    (h72962 : p4524)
    (h52163 : (¬ p2241) ∨ (¬ p2299) ∨ (¬ p2727) ∨ (¬ p3083) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4420) ∨ (¬ p4524))
    : p2274 ∨ (¬ p3083) ∨ p2156 ∨ p2177 ∨ (¬ p2727) ∨ (¬ p4420) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4524 := h72962;
    (Or.elim h52163 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u10)))))))))))))))))

theorem step95162 (p2241 p2459 p2727 p2881 p3051 p3343 p3556 p3570 p4332 p4348 p4524 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73418 : p3570 ∨ p2881)
    (h73414 : p3556 ∨ p3051)
    (h72962 : p4524)
    (h56558 : (¬ p2241) ∨ (¬ p2727) ∨ (¬ p3343) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4332) ∨ (¬ p4348) ∨ (¬ p4524))
    : (¬ p3343) ∨ (¬ p4332) ∨ p2459 ∨ (¬ p2727) ∨ p2881 ∨ p3051 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p4524 := h72962;
    (Or.elim h56558 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u10)))))))))))))))))

theorem step95173 (p2245 p2630 p2737 p2743 p2810 p3166 p3172 p3537 p4967 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73356 : p3172 ∨ p3166)
    (h73316 : p2810 ∨ p2630)
    (h46289 : (¬ p2245) ∨ (¬ p2743) ∨ (¬ p2810) ∨ (¬ p3172) ∨ (¬ p3537) ∨ (¬ p4967))
    : (¬ p2245) ∨ (¬ p4967) ∨ (¬ p3537) ∨ p2737 ∨ p3166 ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4967 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u8 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h46289 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step95174 (p2098 p2104 p3166 p3172 p4236 p4967 : Prop)
    (h73203 : (¬ p2098) ∨ (¬ p2104))
    (h73356 : p3172 ∨ p3166)
    (h29161 : p2104 ∨ (¬ p3172) ∨ (¬ p4236) ∨ (¬ p4967))
    : (¬ p4236) ∨ (¬ p2098) ∨ (¬ p4967) ∨ p3166 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4236 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4967 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2104) := (Or.elim h73203 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u5 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h29161 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step95181 (p2696 p2737 p2743 p3256 p3537 p3589 p4967 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h52334 : (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3256) ∨ (¬ p3537) ∨ (¬ p3589) ∨ (¬ p4967))
    : (¬ p3537) ∨ (¬ p3256) ∨ (¬ p2696) ∨ (¬ p4967) ∨ p2737 ∨ (¬ p3589) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3537 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4967 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h52334 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step95182 (p3256 p3609 p4118 p4340 p4967 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h73519 : (¬ p3256) ∨ (¬ p4118))
    (h25569 : p4118 ∨ (¬ p4340) ∨ (¬ p4967))
    : p3609 ∨ (¬ p3256) ∨ (¬ p4967) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4967 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p4118) := (Or.elim h73519 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h25569 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step95184 (p2088 p2112 p3537 p3599 p4379 p5339 : Prop)
    (h73572 : p4379 ∨ p3599)
    (h41214 : (¬ p2088) ∨ (¬ p2112) ∨ (¬ p3537) ∨ (¬ p4379) ∨ (¬ p5339))
    : (¬ p5339) ∨ (¬ p2112) ∨ (¬ p3537) ∨ (¬ p2088) ∨ p3599 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5339 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2112 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3599) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4379 := (Or.elim h73572 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41214 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step95186 (p2608 p3449 p3860 p3954 p4436 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73481 : (¬ p3449) ∨ (¬ p3860))
    (h24252 : p3860 ∨ (¬ p3954) ∨ (¬ p4436))
    : (¬ p4436) ∨ p2608 ∨ (¬ p3449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4436 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : (¬ p3860) := (Or.elim h73481 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h24252 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u0)))))))

theorem step95196 (p2088 p2241 p2247 p2744 p3073 p4261 p4436 p5242 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h73226 : p2247 ∨ p2241)
    (h52770 : (¬ p2088) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p4261) ∨ (¬ p4436) ∨ (¬ p5242))
    : p3073 ∨ p2241 ∨ (¬ p2744) ∨ (¬ p4436) ∨ (¬ p2088) ∨ (¬ p5242) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4436 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h52770 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step95200 (p2156 p2274 p2396 p2608 p3370 p3399 p3527 p3548 p4366 p4377 p4668 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73404 : p3548 ∨ p3527)
    (h50083 : (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2608) ∨ (¬ p3370) ∨ (¬ p3548) ∨ (¬ p4366) ∨ (¬ p4377) ∨ (¬ p4668))
    : p3399 ∨ (¬ p2396) ∨ (¬ p4668) ∨ (¬ p3370) ∨ (¬ p2274) ∨ p3527 ∨ (¬ p4377) ∨ (¬ p2608) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h50083 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step95201 (p2220 p2459 p2509 p2608 p3146 p3370 p3379 p3452 p4348 p4377 p4438 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73394 : p3452 ∨ p3379)
    (h58686 : (¬ p2220) ∨ (¬ p2509) ∨ (¬ p2608) ∨ (¬ p3146) ∨ (¬ p3370) ∨ (¬ p3452) ∨ (¬ p4348) ∨ (¬ p4377) ∨ (¬ p4438))
    : (¬ p3370) ∨ (¬ p3146) ∨ (¬ p2608) ∨ (¬ p2220) ∨ p2459 ∨ (¬ p4438) ∨ p3379 ∨ (¬ p4377) ∨ (¬ p2509) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3370 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h58686 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step95212 (p2098 p2104 p2598 p3422 p4595 p5369 : Prop)
    (h73204 : p2104 ∨ p2098)
    (h57224 : (¬ p2104) ∨ (¬ p2598) ∨ (¬ p3422) ∨ (¬ p4595) ∨ (¬ p5369))
    : p2098 ∨ (¬ p5369) ∨ (¬ p4595) ∨ (¬ p2598) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : p5369 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4595 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h57224 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step95216 (p2470 p2476 p2528 p2534 p2685 p2753 p2807 p3005 p3146 p3347 p3572 p4117 p5063 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73250 : p2476 ∨ p2470)
    (h73420 : p3572 ∨ p2685)
    (h72089 : (¬ p2534) ∨ (¬ p3146) ∨ (¬ p3572) ∨ (¬ p2753) ∨ (¬ p4117) ∨ (¬ p2476) ∨ (¬ p5063) ∨ (¬ p2807) ∨ (¬ p3005) ∨ (¬ p3347))
    : (¬ p3005) ∨ (¬ p2753) ∨ (¬ p2807) ∨ p2528 ∨ (¬ p4117) ∨ p2470 ∨ (¬ p3146) ∨ p2685 ∨ (¬ p5063) ∨ (¬ p3347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h72089 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step95217 (p2284 p2972 p3136 p3755 p4035 p4040 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h49010 : (¬ p2284) ∨ (¬ p2972) ∨ (¬ p3136) ∨ (¬ p4035) ∨ (¬ p4040))
    : (¬ p4040) ∨ p3755 ∨ (¬ p2972) ∨ (¬ p3136) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4040 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h49010 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step95218 (p2396 p2427 p2982 p4040 p4107 p4235 p4559 p4660 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73514 : p4107 ∨ p2396)
    (h41285 : (¬ p2982) ∨ (¬ p4040) ∨ (¬ p4107) ∨ (¬ p4235) ∨ (¬ p4559) ∨ (¬ p4660))
    : (¬ p4660) ∨ (¬ p4040) ∨ (¬ p4559) ∨ p2427 ∨ p2396 ∨ (¬ p2982) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4660 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4040 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41285 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step95220 (p2946 p2992 p3286 p3292 p3662 p4040 p4322 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73378 : p3292 ∨ p3286)
    (h43398 : (¬ p2946) ∨ (¬ p3292) ∨ (¬ p3662) ∨ (¬ p4040) ∨ (¬ p4322))
    : (¬ p4322) ∨ p2992 ∨ (¬ p2946) ∨ (¬ p4040) ∨ p3286 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4040 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43398 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step95221 (p2946 p2972 p3286 p3292 p4040 p4960 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h53694 : (¬ p2946) ∨ (¬ p2972) ∨ (¬ p3292) ∨ (¬ p4040) ∨ (¬ p4960))
    : (¬ p4040) ∨ p3286 ∨ (¬ p4960) ∨ (¬ p2972) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4040 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h53694 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step95222 (p2946 p3136 p3286 p3292 p4040 p4315 p4322 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73378 : p3292 ∨ p3286)
    (h44984 : (¬ p2946) ∨ (¬ p3292) ∨ (¬ p4040) ∨ (¬ p4315) ∨ (¬ p4322))
    : (¬ p4322) ∨ (¬ p4040) ∨ p3136 ∨ (¬ p2946) ∨ p3286 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4040 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h44984 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step95229 (p3755 p5453 p6121 : Prop)
    (h74457 : p3755 ∨ (¬ p6121))
    (h13915 : p5453 ∨ p6121)
    : p5453 ∨ p3755 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5453) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6121) := (Or.elim h74457 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13915 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95235 (p2187 p2383 p2387 p2427 p4031 p4198 p4558 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h50650 : (¬ p2187) ∨ (¬ p2387) ∨ (¬ p2427) ∨ (¬ p4031) ∨ (¬ p4198) ∨ (¬ p4558))
    : (¬ p4558) ∨ (¬ p2187) ∨ (¬ p4031) ∨ (¬ p4198) ∨ (¬ p2427) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4558 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h50650 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step95237 (p2284 p3745 p5821 : Prop)
    (h74105 : p2284 ∨ (¬ p5821))
    (h11922 : p3745 ∨ p5821)
    : p3745 ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3745) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5821) := (Or.elim h74105 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11922 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95238 (p2284 p4153 p5821 : Prop)
    (h74105 : p2284 ∨ (¬ p5821))
    (h11924 : p4153 ∨ p5821)
    : p4153 ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4153) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5821) := (Or.elim h74105 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11924 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95239 (p2284 p4563 p5821 : Prop)
    (h74105 : p2284 ∨ (¬ p5821))
    (h11925 : p4563 ∨ p5821)
    : p4563 ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4563) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5821) := (Or.elim h74105 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11925 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95241 (p2352 p2459 p3564 p4133 p4137 p4171 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h40982 : (¬ p2352) ∨ (¬ p2459) ∨ (¬ p4133) ∨ (¬ p4137) ∨ (¬ p4171))
    : p3564 ∨ (¬ p4171) ∨ (¬ p2459) ∨ (¬ p2352) ∨ (¬ p4133) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : p4171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h40982 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step95242 (p2132 p2187 p2459 p2509 p2528 p2534 p2753 p2860 p4133 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h72091 : (¬ p2187) ∨ (¬ p2534) ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p4133) ∨ (¬ p2509) ∨ (¬ p2459) ∨ (¬ p2753))
    : (¬ p2753) ∨ (¬ p2509) ∨ (¬ p2860) ∨ (¬ p2459) ∨ (¬ p2187) ∨ (¬ p4133) ∨ p2528 ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2753 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h72091 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step95243 (p2098 p2104 p2241 p2459 p2641 p2668 p3609 p4133 p4340 p4736 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h73204 : p2104 ∨ p2098)
    (h62983 : (¬ p2104) ∨ (¬ p2241) ∨ (¬ p2459) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p4133) ∨ (¬ p4340) ∨ (¬ p4736))
    : p3609 ∨ (¬ p2668) ∨ p2098 ∨ (¬ p4133) ∨ (¬ p2641) ∨ (¬ p2241) ∨ (¬ p4736) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h62983 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step95244 (p2459 p2470 p2476 p2528 p2534 p2608 p3063 p3093 p3347 p3954 p4133 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73268 : p2534 ∨ p2528)
    (h73250 : p2476 ∨ p2470)
    (h72092 : (¬ p3347) ∨ (¬ p2459) ∨ (¬ p4133) ∨ (¬ p2476) ∨ (¬ p3093) ∨ (¬ p3954) ∨ (¬ p3063) ∨ (¬ p2534))
    : (¬ p3063) ∨ p2608 ∨ (¬ p4133) ∨ (¬ p3347) ∨ p2528 ∨ (¬ p3093) ∨ (¬ p2459) ∨ p2470 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h72092 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (False.elim (r6 u9)))))))))))))))))

theorem step95245 (p2459 p2528 p2534 p2608 p2819 p2829 p3389 p3540 p4133 p4186 p5193 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73402 : p3540 ∨ p3389)
    (h64088 : (¬ p2459) ∨ (¬ p2534) ∨ (¬ p2608) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3540) ∨ (¬ p4133) ∨ (¬ p4186) ∨ (¬ p5193))
    : (¬ p2829) ∨ p2528 ∨ (¬ p4133) ∨ (¬ p5193) ∨ (¬ p2459) ∨ (¬ p2608) ∨ (¬ p4186) ∨ p3389 ∨ (¬ p2819) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4186 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64088 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step95249 (p2839 p3537 p4242 p4744 : Prop)
    (h73538 : p4242 ∨ p3537)
    (h29857 : (¬ p2839) ∨ (¬ p4242) ∨ (¬ p4744))
    : p3537 ∨ (¬ p4744) ∨ (¬ p2839) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3537) := (fun h => hn (Or.inl h));
    let u1 : p4744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4242 := (Or.elim h73538 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h29857 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step95252 (p2860 p3758 p4019 p4509 p4744 p5568 : Prop)
    (h73456 : p3758 ∨ p2860)
    (h50436 : (¬ p3758) ∨ (¬ p4019) ∨ (¬ p4509) ∨ (¬ p4744) ∨ (¬ p5568))
    : (¬ p5568) ∨ (¬ p4019) ∨ (¬ p4744) ∨ (¬ p4509) ∨ p2860 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5568 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50436 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step95256 (p3105 p3212 p4019 p4385 p4744 p5568 : Prop)
    (h73576 : p4385 ∨ p3105)
    (h47870 : (¬ p3212) ∨ (¬ p4019) ∨ (¬ p4385) ∨ (¬ p4744) ∨ (¬ p5568))
    : (¬ p4019) ∨ (¬ p5568) ∨ p3105 ∨ (¬ p4744) ∨ (¬ p3212) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4019 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3105) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4385 := (Or.elim h73576 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47870 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step95263 (p2230 p2427 p2696 p3005 p3246 p3256 p3365 p3366 p3519 p3877 p3950 p4118 p4376 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73390 : p3365 ∨ p2696)
    (h73520 : p4118 ∨ p3256)
    (h64667 : (¬ p2230) ∨ (¬ p2427) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4376))
    : p3005 ∨ (¬ p2230) ∨ (¬ p3366) ∨ (¬ p2427) ∨ p2696 ∨ (¬ p3246) ∨ (¬ p3519) ∨ p3256 ∨ (¬ p3950) ∨ (¬ p4376) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64667 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step95265 (p2573 p2696 p3005 p3365 p3366 p3461 p3519 p3564 p3877 p4376 p5123 p5600 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73390 : p3365 ∨ p2696)
    (h42592 : (¬ p2573) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3461) ∨ (¬ p3519) ∨ (¬ p3564) ∨ (¬ p3877) ∨ (¬ p4376) ∨ (¬ p5123) ∨ (¬ p5600))
    : p3005 ∨ (¬ p3461) ∨ (¬ p2573) ∨ (¬ p3366) ∨ (¬ p3564) ∨ (¬ p4376) ∨ p2696 ∨ (¬ p3519) ∨ (¬ p5600) ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h42592 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step95266 (p2608 p2737 p3093 p3591 p4842 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h71008 : (¬ p3591) ∨ (¬ p4842) ∨ (¬ p2737) ∨ (¬ p2608))
    : p3093 ∨ (¬ p2737) ∨ (¬ p4842) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h71008 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step95271 (p2122 p2396 p2608 p3093 p3591 p3822 p3918 p4107 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73514 : p4107 ∨ p2396)
    (h73472 : p3822 ∨ p2122)
    (h57468 : (¬ p2608) ∨ (¬ p3591) ∨ (¬ p3822) ∨ (¬ p3918) ∨ (¬ p4107))
    : p3093 ∨ (¬ p3918) ∨ p2396 ∨ (¬ p2608) ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p3918 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h57468 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step95275 (p2177 p2717 p2774 p3309 p3659 p3918 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h48473 : (¬ p2177) ∨ (¬ p2774) ∨ (¬ p3309) ∨ (¬ p3659) ∨ (¬ p3918))
    : (¬ p3309) ∨ p2717 ∨ (¬ p2177) ∨ (¬ p2774) ∨ (¬ p3918) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3918 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h48473 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step95277 (p2295 p2696 p2774 p3309 p3365 p3568 p3918 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h73416 : p3568 ∨ p2295)
    (h51986 : (¬ p2774) ∨ (¬ p3309) ∨ (¬ p3365) ∨ (¬ p3568) ∨ (¬ p3918))
    : (¬ p3309) ∨ p2696 ∨ (¬ p3918) ∨ (¬ p2774) ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3918 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51986 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step95278 (p2246 p2459 p2608 p2744 p2807 p2819 p3093 p3256 p3591 p3918 p4044 p4348 p4358 p4503 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h73432 : p3591 ∨ p3093)
    (h73562 : p4348 ∨ p2459)
    (h54491 : (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2807) ∨ (¬ p3256) ∨ (¬ p3591) ∨ (¬ p3918) ∨ (¬ p4044) ∨ (¬ p4348) ∨ (¬ p4358) ∨ (¬ p4503))
    : (¬ p2246) ∨ (¬ p4044) ∨ (¬ p3918) ∨ p2819 ∨ p3093 ∨ p2459 ∨ (¬ p2807) ∨ (¬ p2744) ∨ (¬ p2608) ∨ (¬ p3256) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3918 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u13 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h54491 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u13))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u11))) (fun r9 => (False.elim (r9 u10)))))))))))))))))))))))

theorem step95280 (p2608 p2761 p3019 p3093 p3266 p3343 p3359 p3516 p3543 p3591 p3918 p4337 p4444 p4697 p4793 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73388 : p3359 ∨ p3343)
    (h73432 : p3591 ∨ p3093)
    (h61175 : (¬ p2608) ∨ (¬ p2761) ∨ (¬ p3019) ∨ (¬ p3359) ∨ (¬ p3516) ∨ (¬ p3543) ∨ (¬ p3591) ∨ (¬ p3918) ∨ (¬ p4337) ∨ (¬ p4444) ∨ (¬ p4697) ∨ (¬ p4793))
    : p3266 ∨ (¬ p2761) ∨ (¬ p3516) ∨ (¬ p4697) ∨ (¬ p2608) ∨ p3343 ∨ (¬ p3019) ∨ (¬ p4793) ∨ p3093 ∨ (¬ p3543) ∨ (¬ p4337) ∨ (¬ p3918) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4793 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3543 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4337 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3918 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u13 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u14 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h61175 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u13))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u14))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u3))) (fun r10 => (False.elim (r10 u7)))))))))))))))))))))))))

theorem step95282 (p2504 p2598 p2774 p3016 p3055 p3574 p3918 p4753 : Prop)
    (h73350 : p3055 ∨ p2598)
    (h73422 : p3574 ∨ p3016)
    (h59688 : (¬ p2504) ∨ (¬ p2774) ∨ (¬ p3055) ∨ (¬ p3574) ∨ (¬ p3918) ∨ (¬ p4753))
    : (¬ p3918) ∨ (¬ p2774) ∨ (¬ p2504) ∨ p2598 ∨ p3016 ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3918 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h59688 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step95285 (p2417 p2608 p2761 p3093 p3389 p3519 p3591 p3918 p4329 p4376 p5254 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h64719 : (¬ p2417) ∨ (¬ p2608) ∨ (¬ p2761) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p3591) ∨ (¬ p3918) ∨ (¬ p4329) ∨ (¬ p4376) ∨ (¬ p5254))
    : (¬ p4329) ∨ (¬ p2608) ∨ (¬ p3389) ∨ (¬ p2761) ∨ (¬ p3519) ∨ (¬ p3918) ∨ p3093 ∨ (¬ p5254) ∨ (¬ p4376) ∨ (¬ p2417) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4329 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3918 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h64719 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step95286 (p2608 p2819 p3063 p3093 p3589 p3918 p4358 p4866 p5014 : Prop)
    (h73876 : p5014 ∨ p3093)
    (h73564 : p4358 ∨ p2819)
    (h66698 : (¬ p5014) ∨ (¬ p3063) ∨ (¬ p2608) ∨ (¬ p3589) ∨ (¬ p4866) ∨ (¬ p3918) ∨ (¬ p4358))
    : (¬ p3063) ∨ p3093 ∨ (¬ p3589) ∨ (¬ p3918) ∨ p2819 ∨ (¬ p4866) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3918 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4866 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5014 := (Or.elim h73876 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h66698 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u8)))))))))))))))

theorem step95289 (p2318 p2819 p3516 p3631 p3821 p3918 p4358 p4452 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73564 : p4358 ∨ p2819)
    (h72093 : (¬ p3631) ∨ (¬ p4358) ∨ (¬ p2318) ∨ (¬ p3918) ∨ (¬ p4452) ∨ (¬ p3821))
    : (¬ p3631) ∨ (¬ p4452) ∨ p3516 ∨ p2819 ∨ (¬ p3918) ∨ (¬ p2318) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3918 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2318 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h72093 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step95290 (p2819 p3918 p4075 p4358 p4452 p4710 p5503 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h72094 : (¬ p4075) ∨ (¬ p4358) ∨ (¬ p5503) ∨ (¬ p3918) ∨ (¬ p4710) ∨ (¬ p4452))
    : (¬ p4075) ∨ (¬ p5503) ∨ (¬ p4710) ∨ p2819 ∨ (¬ p3918) ∨ (¬ p4452) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4075 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3918 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h72094 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step95298 (p2122 p2563 p2982 p3319 p3822 p3918 p4033 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h73472 : p3822 ∨ p2122)
    (h46412 : (¬ p2563) ∨ (¬ p3319) ∨ (¬ p3822) ∨ (¬ p3918) ∨ (¬ p4033) ∨ (¬ p4948))
    : p2982 ∨ (¬ p3319) ∨ (¬ p2563) ∨ (¬ p4033) ∨ p2122 ∨ (¬ p3918) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4033 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3918 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46412 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step95301 (p3323 p4367 p5277 : Prop)
    (h73986 : p5277 ∨ (¬ p3323))
    (h8985 : p4367 ∨ (¬ p5277))
    : p4367 ∨ (¬ p3323) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4367) := (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5277 := (Or.elim h73986 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h8985 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step95302 (p3323 p4421 p5277 : Prop)
    (h73986 : p5277 ∨ (¬ p3323))
    (h8986 : p4421 ∨ (¬ p5277))
    : p4421 ∨ (¬ p3323) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4421) := (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5277 := (Or.elim h73986 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h8986 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step95304 (p3323 p5277 p5279 : Prop)
    (h73986 : p5277 ∨ (¬ p3323))
    (h8989 : (¬ p5277) ∨ p5279)
    : (¬ p3323) ∨ p5279 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5279) := (fun h => hn (Or.inr h));
    let u2 : p5277 := (Or.elim h73986 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h8989 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step95305 (p2331 p2963 p3286 p3292 p5274 : Prop)
    (h73377 : (¬ p3286) ∨ (¬ p3292))
    (h73338 : p2963 ∨ p2331)
    (h22781 : (¬ p2963) ∨ p3292 ∨ (¬ p5274))
    : (¬ p3286) ∨ p2331 ∨ (¬ p5274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3286 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3292) := (Or.elim h73377 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h22781 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step95313 (p3440 p3449 p3860 p4374 p4439 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h6891 : (¬ p3440) ∨ (¬ p3860) ∨ (¬ p4374) ∨ (¬ p4439))
    : p3449 ∨ (¬ p3440) ∨ (¬ p4374) ∨ (¬ p4439) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3449) := (fun h => hn (Or.inl h));
    let u1 : p3440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4374 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4439 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h6891 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step95314 (p3005 p3136 p3171 p3266 p3680 p4315 p4374 p4387 p4444 p4461 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73550 : p4315 ∨ p3136)
    (h47116 : (¬ p3005) ∨ (¬ p3171) ∨ (¬ p3680) ∨ (¬ p4315) ∨ (¬ p4374) ∨ (¬ p4387) ∨ (¬ p4444) ∨ (¬ p4461))
    : p3266 ∨ (¬ p3680) ∨ (¬ p4461) ∨ (¬ p3005) ∨ (¬ p3171) ∨ (¬ p4374) ∨ p3136 ∨ (¬ p4387) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4374 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h47116 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step95316 (p2307 p2553 p2588 p3125 p3958 p5378 p5379 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h59142 : (¬ p2307) ∨ (¬ p2588) ∨ (¬ p3125) ∨ (¬ p3958) ∨ (¬ p5378) ∨ (¬ p5379))
    : (¬ p3125) ∨ (¬ p2307) ∨ (¬ p3958) ∨ (¬ p5379) ∨ (¬ p5378) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5378 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h59142 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step95319 (p3461 p3773 p4191 p5379 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h25050 : p3773 ∨ (¬ p4191) ∨ (¬ p5379))
    : p3773 ∨ p3461 ∨ (¬ p5379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3773) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h25050 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step95329 (p2264 p4548 p5815 : Prop)
    (h74097 : p2264 ∨ (¬ p5815))
    (h11888 : p4548 ∨ p5815)
    : p4548 ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4548) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2264) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5815) := (Or.elim h74097 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11888 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95330 (p2493 p2499 p2584 p3564 p3654 p4137 p5194 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h73260 : p2499 ∨ p2493)
    (h59209 : (¬ p2499) ∨ (¬ p2584) ∨ (¬ p3654) ∨ (¬ p4137) ∨ (¬ p5194))
    : (¬ p3654) ∨ p3564 ∨ p2493 ∨ (¬ p5194) ∨ (¬ p2584) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h59209 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step95331 (p2156 p2406 p2563 p3238 p4110 p4399 p5194 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h73516 : p4110 ∨ p2563)
    (h49333 : (¬ p2156) ∨ (¬ p3238) ∨ (¬ p4110) ∨ (¬ p4399) ∨ (¬ p5194))
    : (¬ p2156) ∨ (¬ p4399) ∨ (¬ p5194) ∨ p2406 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49333 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step95332 (p2088 p2459 p2717 p3659 p4348 p4590 p5261 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h73562 : p4348 ∨ p2459)
    (h41031 : (¬ p2088) ∨ (¬ p3659) ∨ (¬ p4348) ∨ (¬ p4590) ∨ (¬ p5261))
    : p2717 ∨ (¬ p4590) ∨ p2459 ∨ (¬ p2088) ∨ (¬ p5261) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p4590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41031 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step95335 (p2254 p2459 p2651 p2657 p3016 p3399 p3527 p3564 p3574 p4137 p4604 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h73422 : p3574 ∨ p3016)
    (h73288 : p2657 ∨ p2651)
    (h57288 : (¬ p2254) ∨ (¬ p2459) ∨ (¬ p2657) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3574) ∨ (¬ p4137) ∨ (¬ p4604))
    : (¬ p3527) ∨ p3564 ∨ p3016 ∨ (¬ p4604) ∨ (¬ p2459) ∨ (¬ p3399) ∨ p2651 ∨ (¬ p2254) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h57288 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step95339 (p2341 p2459 p2493 p2499 p2598 p2707 p3055 p3564 p3577 p4030 p4137 p4604 p4734 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h73350 : p3055 ∨ p2598)
    (h72735 : p4734)
    (h73260 : p2499 ∨ p2493)
    (h60524 : (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2499) ∨ (¬ p2707) ∨ (¬ p3055) ∨ (¬ p3577) ∨ (¬ p4030) ∨ (¬ p4137) ∨ (¬ p4604) ∨ (¬ p4734))
    : (¬ p2707) ∨ (¬ p4030) ∨ (¬ p2459) ∨ p3564 ∨ p2598 ∨ (¬ p2341) ∨ (¬ p3577) ∨ p2493 ∨ (¬ p4604) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p4734 := h72735;
    let u12 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h60524 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u11)))))))))))))))))))))

theorem step95340 (p2598 p2946 p3055 p3146 p3156 p3422 p3564 p3584 p4137 p4604 p4786 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h73350 : p3055 ∨ p2598)
    (h73524 : p4137 ∨ p3564)
    (h52150 : (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4604) ∨ (¬ p4786))
    : (¬ p2946) ∨ p3422 ∨ (¬ p3146) ∨ (¬ p3156) ∨ p2598 ∨ (¬ p4604) ∨ p3564 ∨ (¬ p4786) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h52150 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step95343 (p2284 p3115 p3952 p4205 p4208 : Prop)
    (h73533 : (¬ p3115) ∨ (¬ p4208))
    (h73496 : p3952 ∨ p2284)
    (h27216 : (¬ p3952) ∨ (¬ p4205) ∨ p4208)
    : (¬ p3115) ∨ (¬ p4205) ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4205 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4208) := (Or.elim h73533 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h27216 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u3 r1)))))))

theorem step95348 (p2156 p2972 p3645 p3646 p4205 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h37467 : (¬ p2972) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p4205))
    : (¬ p2972) ∨ (¬ p4205) ∨ (¬ p3645) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4205 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h37467 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step95349 (p2156 p3212 p3646 p4205 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h27215 : (¬ p3212) ∨ (¬ p3646) ∨ (¬ p4205))
    : (¬ p3212) ∨ (¬ p4205) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3212 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4205 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h27215 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step95353 (p2563 p2982 p4110 p4205 p4948 : Prop)
    (h73845 : (¬ p2982) ∨ (¬ p4948))
    (h73516 : p4110 ∨ p2563)
    (h29775 : (¬ p4110) ∨ (¬ p4205) ∨ p4948)
    : (¬ p2982) ∨ (¬ p4205) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4205 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4948) := (Or.elim h73845 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h29775 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u3 r1)))))))

theorem step95369 (p2427 p3051 p3346 p4235 p4399 p4949 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h50911 : (¬ p3051) ∨ (¬ p3346) ∨ (¬ p4235) ∨ (¬ p4399) ∨ (¬ p4949))
    : (¬ p3051) ∨ p2427 ∨ (¬ p4949) ∨ (¬ p3346) ∨ (¬ p4399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4949 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h50911 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step95370 (p2156 p2470 p2476 p2563 p4110 p4399 p4608 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h73516 : p4110 ∨ p2563)
    (h42195 : (¬ p2156) ∨ (¬ p2476) ∨ (¬ p4110) ∨ (¬ p4399) ∨ (¬ p4608))
    : (¬ p4399) ∨ p2470 ∨ (¬ p2156) ∨ p2563 ∨ (¬ p4608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2470) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42195 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step95377 (p2241 p2247 p4187 p4620 p5190 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h50706 : (¬ p2247) ∨ (¬ p4187) ∨ p4620 ∨ (¬ p5190))
    : p4620 ∨ (¬ p4187) ∨ p2241 ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4620) := (fun h => hn (Or.inl h));
    let u1 : p4187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50706 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step95379 (p2241 p2247 p2459 p2641 p2911 p3323 p3389 p4037 p4154 p4604 p5190 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73508 : p4037 ∨ p3323)
    (h73226 : p2247 ∨ p2241)
    (h62715 : (¬ p2247) ∨ (¬ p2459) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4604) ∨ (¬ p5190))
    : p2641 ∨ (¬ p5190) ∨ p3323 ∨ (¬ p4604) ∨ (¬ p2911) ∨ (¬ p2459) ∨ (¬ p3389) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h62715 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step95382 (p2230 p2241 p2247 p2982 p2996 p3680 p4391 p4831 p5190 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h55262 : (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2982) ∨ (¬ p2996) ∨ (¬ p3680) ∨ (¬ p4391) ∨ (¬ p4831) ∨ (¬ p5190))
    : (¬ p2230) ∨ (¬ p2982) ∨ (¬ p3680) ∨ (¬ p4391) ∨ (¬ p5190) ∨ (¬ p2996) ∨ (¬ p4831) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h55262 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step95384 (p2230 p2241 p2247 p2563 p3125 p3189 p3256 p4118 p4330 p4360 p5190 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h73226 : p2247 ∨ p2241)
    (h73566 : p4360 ∨ p3189)
    (h58435 : (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2563) ∨ (¬ p3125) ∨ (¬ p4118) ∨ (¬ p4330) ∨ (¬ p4360) ∨ (¬ p5190))
    : p3256 ∨ p2241 ∨ (¬ p2563) ∨ (¬ p4330) ∨ (¬ p2230) ∨ (¬ p5190) ∨ (¬ p3125) ∨ p3189 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h58435 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step95387 (p2177 p2553 p2573 p3073 p3256 p3449 p3860 p4041 p4261 p5190 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h73482 : p3860 ∨ p3449)
    (h62579 : (¬ p2177) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3256) ∨ (¬ p3860) ∨ (¬ p4041) ∨ (¬ p4261) ∨ (¬ p5190))
    : p3073 ∨ p3449 ∨ (¬ p5190) ∨ (¬ p4041) ∨ (¬ p2553) ∨ (¬ p3256) ∨ (¬ p2177) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h62579 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step95388 (p3093 p5018 p5980 : Prop)
    (h74309 : p3093 ∨ (¬ p5980))
    (h12869 : p5018 ∨ p5980)
    : p5018 ∨ p3093 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5018) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5980) := (Or.elim h74309 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12869 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95389 (p3093 p5016 p5980 : Prop)
    (h74309 : p3093 ∨ (¬ p5980))
    (h12871 : p5016 ∨ p5980)
    : p5016 ∨ p3093 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5016) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5980) := (Or.elim h74309 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12871 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95390 (p3093 p5017 p5980 : Prop)
    (h74309 : p3093 ∨ (¬ p5980))
    (h12872 : p5017 ∨ p5980)
    : p5017 ∨ p3093 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5017) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5980) := (Or.elim h74309 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12872 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95391 (p3093 p5015 p5980 : Prop)
    (h74309 : p3093 ∨ (¬ p5980))
    (h12873 : p5015 ∨ p5980)
    : p5015 ∨ p3093 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5015) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5980) := (Or.elim h74309 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12873 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95393 (p2493 p2499 p3379 p3449 p3452 p4598 p4687 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73260 : p2499 ∨ p2493)
    (h64478 : (¬ p2499) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4598) ∨ (¬ p4687))
    : p3379 ∨ (¬ p4687) ∨ p2493 ∨ (¬ p3449) ∨ (¬ p4598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p4687 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h64478 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step95394 (p2608 p3422 p3449 p3641 p3874 p3954 p4687 : Prop)
    (h73484 : p3874 ∨ p3641)
    (h73498 : p3954 ∨ p2608)
    (h47980 : (¬ p3422) ∨ (¬ p3449) ∨ (¬ p3874) ∨ (¬ p3954) ∨ (¬ p4687))
    : (¬ p4687) ∨ p3641 ∨ (¬ p3449) ∨ p2608 ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4687 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47980 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step95396 (p2528 p3073 p4261 p4687 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h19969 : (¬ p2528) ∨ (¬ p4261) ∨ (¬ p4687))
    : p3073 ∨ (¬ p4687) ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p4687 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h19969 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step95408 (p2440 p3379 p3449 p3452 p4116 p4610 p4687 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h41694 : (¬ p2440) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4116) ∨ (¬ p4610) ∨ (¬ p4687))
    : (¬ p4116) ∨ p3379 ∨ (¬ p2440) ∨ (¬ p3449) ∨ (¬ p4687) ∨ (¬ p4610) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4116 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4687 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4610 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41694 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step95410 (p3083 p3379 p3449 p3452 p4256 p4687 p4814 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73542 : p4256 ∨ p3083)
    (h50728 : (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4256) ∨ (¬ p4687) ∨ (¬ p4814))
    : (¬ p4687) ∨ (¬ p3449) ∨ p3379 ∨ (¬ p4814) ∨ p3083 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4687 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50728 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step95414 (p2406 p3238 p3379 p3449 p3452 p4610 p4687 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73374 : p3238 ∨ p2406)
    (h55731 : (¬ p3238) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4610) ∨ (¬ p4687))
    : (¬ p4687) ∨ (¬ p3449) ∨ p3379 ∨ p2406 ∨ (¬ p4610) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4687 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4610 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55731 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step95419 (p2651 p2657 p3166 p3641 p3874 p4687 p4750 p5074 : Prop)
    (h73484 : p3874 ∨ p3641)
    (h73288 : p2657 ∨ p2651)
    (h63055 : (¬ p2657) ∨ (¬ p3166) ∨ (¬ p3874) ∨ (¬ p4687) ∨ (¬ p4750) ∨ (¬ p5074))
    : (¬ p4687) ∨ (¬ p5074) ∨ p3641 ∨ p2651 ∨ (¬ p4750) ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4687 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5074 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63055 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step95420 (p2241 p2247 p3449 p4149 p4687 p5568 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h47055 : (¬ p2247) ∨ (¬ p3449) ∨ (¬ p4149) ∨ (¬ p4687) ∨ (¬ p5568))
    : (¬ p4149) ∨ (¬ p5568) ∨ p2241 ∨ (¬ p3449) ∨ (¬ p4687) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4149 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4687 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47055 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step95424 (p2363 p2383 p2387 p2598 p2778 p3367 p3585 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73428 : p3585 ∨ p3367)
    (h73246 : p2387 ∨ p2383)
    (h43014 : (¬ p2387) ∨ (¬ p2598) ∨ (¬ p2778) ∨ (¬ p3585) ∨ (¬ p4347))
    : (¬ p2778) ∨ p2363 ∨ p3367 ∨ (¬ p2598) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2778 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43014 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step95426 (p2668 p2696 p2778 p3323 p3324 p3654 p3946 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h73492 : p3946 ∨ p3654)
    (h62711 : (¬ p2696) ∨ (¬ p2778) ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p3946))
    : (¬ p3323) ∨ (¬ p2778) ∨ (¬ p2696) ∨ p2668 ∨ p3654 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62711 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step95427 (p2241 p2247 p2363 p2383 p2387 p2744 p2778 p3083 p3366 p3379 p3487 p3609 p4347 p5375 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73226 : p2247 ∨ p2241)
    (h73246 : p2387 ∨ p2383)
    (h57334 : (¬ p2247) ∨ (¬ p2387) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p3083) ∨ (¬ p3366) ∨ (¬ p3379) ∨ (¬ p3487) ∨ (¬ p3609) ∨ (¬ p4347) ∨ (¬ p5375))
    : p2363 ∨ p2241 ∨ (¬ p3083) ∨ (¬ p3366) ∨ (¬ p5375) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p3609) ∨ (¬ p3379) ∨ (¬ p3487) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u13 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h57334 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u11))) (fun r9 => (False.elim (r9 u4)))))))))))))))))))))))

theorem step95430 (p2383 p2387 p2696 p2778 p2819 p4842 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h62372 : (¬ p2387) ∨ (¬ p2696) ∨ (¬ p2778) ∨ (¬ p2819) ∨ (¬ p4842))
    : (¬ p2778) ∨ (¬ p2819) ∨ (¬ p2696) ∨ (¬ p4842) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2778 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62372 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step95434 (p2177 p2230 p2299 p2307 p2313 p2440 p2459 p2778 p3343 p3366 p3519 p4332 p4348 p4376 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73238 : p2313 ∨ p2307)
    (h73234 : p2299 ∨ p2177)
    (h42366 : (¬ p2230) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2440) ∨ (¬ p2778) ∨ (¬ p3343) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p4332) ∨ (¬ p4348) ∨ (¬ p4376))
    : (¬ p2230) ∨ p2459 ∨ (¬ p3366) ∨ (¬ p4332) ∨ (¬ p2440) ∨ p2307 ∨ (¬ p3343) ∨ (¬ p3519) ∨ p2177 ∨ (¬ p2778) ∨ (¬ p4376) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h42366 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u11))) (fun r9 => (False.elim (r9 u10)))))))))))))))))))))))

theorem step95435 (p2246 p2363 p2373 p2383 p2387 p2440 p2459 p2542 p2651 p2744 p2778 p3366 p4347 p4902 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73246 : p2387 ∨ p2383)
    (h73270 : p2542 ∨ p2440)
    (h52767 : (¬ p2246) ∨ (¬ p2373) ∨ (¬ p2387) ∨ (¬ p2459) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p3366) ∨ (¬ p4347) ∨ (¬ p4902))
    : (¬ p2778) ∨ p2363 ∨ (¬ p2373) ∨ p2383 ∨ (¬ p2459) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p4902) ∨ p2440 ∨ (¬ p3366) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2778 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h52767 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u13))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u11))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step95436 (p2383 p2387 p2598 p2742 p2778 p3063 p4752 p4759 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h51741 : (¬ p2387) ∨ (¬ p2598) ∨ (¬ p2742) ∨ (¬ p2778) ∨ (¬ p3063) ∨ (¬ p4752) ∨ (¬ p4759))
    : (¬ p3063) ∨ (¬ p2742) ∨ (¬ p2778) ∨ p2383 ∨ (¬ p2598) ∨ (¬ p4752) ∨ (¬ p4759) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h51741 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step95442 (p2264 p2307 p2313 p2778 p3553 p3931 p4260 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h73238 : p2313 ∨ p2307)
    (h54849 : (¬ p2313) ∨ (¬ p2778) ∨ (¬ p3553) ∨ (¬ p3931) ∨ (¬ p4260))
    : (¬ p4260) ∨ (¬ p3931) ∨ (¬ p2778) ∨ p2264 ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4260 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54849 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step95448 (p2383 p2387 p2761 p2778 p2819 p3276 p3355 p3917 p4381 p4419 p4625 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73246 : p2387 ∨ p2383)
    (h42228 : (¬ p2387) ∨ (¬ p2778) ∨ (¬ p2819) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3917) ∨ (¬ p4381) ∨ (¬ p4419) ∨ (¬ p4625))
    : p2761 ∨ (¬ p2819) ∨ (¬ p4625) ∨ p2383 ∨ (¬ p3276) ∨ (¬ p3917) ∨ (¬ p4419) ∨ (¬ p2778) ∨ (¬ p3355) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42228 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step95449 (p2122 p2210 p2241 p2247 p2307 p2313 p2744 p2778 p2972 p3366 p3917 p4397 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73238 : p2313 ∨ p2307)
    (h62836 : (¬ p2122) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2313) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p2972) ∨ (¬ p3366) ∨ (¬ p3917) ∨ (¬ p4397))
    : (¬ p2778) ∨ (¬ p2122) ∨ p2241 ∨ p2307 ∨ (¬ p2210) ∨ (¬ p4397) ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p2972) ∨ (¬ p3917) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2778 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4397 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62836 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step95453 (p2383 p2387 p2427 p2563 p2778 p3051 p3256 p4019 p4118 p4235 p4399 p4419 p4963 p5580 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h73536 : p4235 ∨ p2427)
    (h73520 : p4118 ∨ p3256)
    (h50908 : (¬ p2387) ∨ (¬ p2563) ∨ (¬ p2778) ∨ (¬ p3051) ∨ (¬ p4019) ∨ (¬ p4118) ∨ (¬ p4235) ∨ (¬ p4399) ∨ (¬ p4419) ∨ (¬ p4963) ∨ (¬ p5580))
    : (¬ p4019) ∨ (¬ p5580) ∨ (¬ p2563) ∨ (¬ p3051) ∨ (¬ p2778) ∨ p2383 ∨ p2427 ∨ (¬ p4399) ∨ (¬ p4963) ∨ (¬ p4419) ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4019 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h50908 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u1)))))))))))))))))))))))

theorem step95456 (p2922 p2928 p3073 p3609 p3695 p4340 p4359 p4644 p4688 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73558 : p4340 ∨ p3609)
    (h64740 : (¬ p2928) ∨ (¬ p3073) ∨ (¬ p3695) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4644) ∨ (¬ p4688))
    : (¬ p4688) ∨ (¬ p3695) ∨ (¬ p4644) ∨ p2922 ∨ (¬ p3073) ∨ (¬ p4359) ∨ p3609 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4688 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h64740 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u0)))))))))))))))

theorem step95460 (p2668 p4769 p5896 : Prop)
    (h74201 : p2668 ∨ (¬ p5896))
    (h12360 : p4769 ∨ p5896)
    : p4769 ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4769) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2668) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5896) := (Or.elim h74201 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12360 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95461 (p2427 p4001 p5854 : Prop)
    (h74149 : p2427 ∨ (¬ p5854))
    (h12117 : p4001 ∨ p5854)
    : p4001 ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4001) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5854) := (Or.elim h74149 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12117 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95462 (p2427 p2441 p5854 : Prop)
    (h74149 : p2427 ∨ (¬ p5854))
    (h12119 : p2441 ∨ p5854)
    : p2441 ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2441) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5854) := (Or.elim h74149 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12119 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95465 (p2284 p2946 p3166 p3172 p4312 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h69543 : (¬ p2946) ∨ (¬ p3172) ∨ (¬ p2284) ∨ (¬ p4312))
    : p3166 ∨ (¬ p4312) ∨ (¬ p2284) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : p4312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h69543 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step95466 (p3146 p3256 p3692 p4118 p4312 : Prop)
    (h73519 : (¬ p3256) ∨ (¬ p4118))
    (h73448 : p3692 ∨ p3146)
    (h6676 : (¬ p3692) ∨ p4118 ∨ (¬ p4312))
    : (¬ p3256) ∨ p3146 ∨ (¬ p4312) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4118) := (Or.elim h73519 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h6676 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step95472 (p2088 p2103 p3609 p3857 p4340 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h73479 : (¬ p2088) ∨ (¬ p3857))
    (h6582 : (¬ p2103) ∨ p3857 ∨ (¬ p4340))
    : p3609 ∨ (¬ p2103) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p2103 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p3857) := (Or.elim h73479 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h6582 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step95482 (p2507 p3093 p3564 p3591 p3830 p4137 p5152 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73524 : p4137 ∨ p3564)
    (h49211 : (¬ p2507) ∨ (¬ p3591) ∨ (¬ p3830) ∨ (¬ p4137) ∨ (¬ p5152))
    : (¬ p3830) ∨ (¬ p5152) ∨ (¬ p2507) ∨ p3093 ∨ p3564 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3830 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5152 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2507 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49211 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step95488 (p2440 p2651 p2657 p2807 p3579 p4646 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h42285 : (¬ p2440) ∨ (¬ p2657) ∨ (¬ p2807) ∨ (¬ p3579) ∨ (¬ p4646))
    : (¬ p2440) ∨ p2651 ∨ (¬ p2807) ∨ (¬ p3579) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42285 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step95490 (p2651 p2657 p2807 p3201 p3579 p3876 p4750 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73486 : p3876 ∨ p3201)
    (h49367 : (¬ p2657) ∨ (¬ p2807) ∨ (¬ p3579) ∨ (¬ p3876) ∨ (¬ p4750))
    : p2651 ∨ p3201 ∨ (¬ p2807) ∨ (¬ p3579) ∨ (¬ p4750) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h49367 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step95494 (p2417 p2449 p3579 p3947 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h5862 : (¬ p2417) ∨ (¬ p3579) ∨ (¬ p3947))
    : (¬ p2417) ∨ p2449 ∨ (¬ p3579) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h5862 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step95495 (p2264 p2911 p3553 p3579 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h28913 : (¬ p2911) ∨ (¬ p3553) ∨ (¬ p3579))
    : (¬ p2911) ∨ (¬ p3579) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h28913 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step95499 (p2396 p2807 p3286 p3292 p3579 p4276 p4656 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h41726 : (¬ p2396) ∨ (¬ p2807) ∨ (¬ p3292) ∨ (¬ p3579) ∨ (¬ p4276) ∨ (¬ p4656))
    : (¬ p4656) ∨ (¬ p2396) ∨ (¬ p3579) ∨ (¬ p2807) ∨ p3286 ∨ (¬ p4276) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4656 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41726 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step95506 (p2437 p2933 p3379 p3399 p3452 p3742 p4814 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73452 : p3742 ∨ p2437)
    (h41185 : (¬ p2933) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3742) ∨ (¬ p4814))
    : (¬ p3399) ∨ p3379 ∨ p2437 ∨ (¬ p2933) ∨ (¬ p4814) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2933 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41185 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step95507 (p2417 p2696 p2933 p3005 p3256 p3365 p3366 p3379 p3399 p3452 p3877 p3950 p4118 p4376 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73520 : p4118 ∨ p3256)
    (h73394 : p3452 ∨ p3379)
    (h73390 : p3365 ∨ p2696)
    (h64893 : (¬ p2417) ∨ (¬ p2933) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4376))
    : (¬ p3399) ∨ p3005 ∨ (¬ p4376) ∨ (¬ p3950) ∨ (¬ p2417) ∨ p3256 ∨ p3379 ∨ (¬ p3366) ∨ (¬ p2933) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2933 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h64893 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u13))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step95508 (p2417 p2761 p2933 p3379 p3399 p3452 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h65025 : (¬ p2417) ∨ (¬ p2761) ∨ (¬ p2933) ∨ (¬ p3399) ∨ (¬ p3452))
    : (¬ p3399) ∨ (¬ p2761) ∨ (¬ p2933) ∨ (¬ p2417) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2933 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h65025 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step95512 (p2459 p2911 p2933 p3379 p3399 p3452 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h47286 : (¬ p2459) ∨ (¬ p2911) ∨ (¬ p2933) ∨ (¬ p3399) ∨ (¬ p3452))
    : (¬ p3399) ∨ p3379 ∨ (¬ p2459) ∨ (¬ p2933) ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2933 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47286 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step95514 (p2933 p3201 p3379 p3399 p3452 p3876 p5217 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73486 : p3876 ∨ p3201)
    (h49984 : (¬ p2933) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3876) ∨ (¬ p5217))
    : (¬ p3399) ∨ p3379 ∨ p3201 ∨ (¬ p2933) ∨ (¬ p5217) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2933 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5217 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h49984 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step95529 (p2417 p2933 p3631 p3817 p4278 : Prop)
    (h73545 : (¬ p2417) ∨ (¬ p4278))
    (h73468 : p3817 ∨ p3631)
    (h28659 : (¬ p2933) ∨ (¬ p3817) ∨ p4278)
    : (¬ p2417) ∨ p3631 ∨ (¬ p2933) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3631) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2933 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4278) := (Or.elim h73545 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h28659 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (u3 r1)))))))

theorem step95532 (p2911 p2933 p3527 p3548 p3644 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h73433 : (¬ p2911) ∨ (¬ p3644))
    (h5322 : (¬ p2933) ∨ (¬ p3548) ∨ p3644)
    : (¬ p2933) ∨ p3527 ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2933 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3527) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : (¬ p3644) := (Or.elim h73433 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h5322 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (u4 r1)))))))

theorem step95541 (p2441 p2563 p2933 p3246 p3631 p3817 p4555 : Prop)
    (h73468 : p3817 ∨ p3631)
    (h63306 : (¬ p2441) ∨ (¬ p2563) ∨ (¬ p2933) ∨ (¬ p3246) ∨ (¬ p3817) ∨ (¬ p4555))
    : p3631 ∨ (¬ p3246) ∨ (¬ p2933) ∨ (¬ p4555) ∨ (¬ p2563) ∨ (¬ p2441) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2933 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h63306 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step95544 (p2881 p2933 p3527 p3548 p3569 p3570 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h73417 : (¬ p2881) ∨ (¬ p3570))
    (h31438 : (¬ p2933) ∨ (¬ p3548) ∨ (¬ p3569) ∨ p3570)
    : (¬ p2933) ∨ p3527 ∨ (¬ p3569) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2933 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3527) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : (¬ p3570) := (Or.elim h73417 (fun q0 => (False.elim (q0 u3))) (fun r0 => r0));
    (Or.elim h31438 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (u5 r2)))))))))

theorem step95553 (p2440 p2933 p3019 p3073 p3256 p3544 p4261 p4341 p4646 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h63253 : (¬ p2440) ∨ (¬ p2933) ∨ (¬ p3019) ∨ (¬ p3256) ∨ (¬ p3544) ∨ (¬ p4261) ∨ (¬ p4341) ∨ (¬ p4646))
    : (¬ p4341) ∨ p3073 ∨ (¬ p2933) ∨ (¬ p3544) ∨ (¬ p3019) ∨ (¬ p3256) ∨ (¬ p4646) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2933 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3544 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h63253 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step95554 (p2651 p2657 p2850 p3333 p3343 p3359 p3684 : Prop)
    (h73388 : p3359 ∨ p3343)
    (h73442 : p3684 ∨ p2850)
    (h73288 : p2657 ∨ p2651)
    (h47105 : (¬ p2657) ∨ (¬ p3333) ∨ (¬ p3359) ∨ (¬ p3684))
    : (¬ p3333) ∨ p3343 ∨ p2850 ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47105 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step95558 (p2598 p3016 p3333 p3343 p3359 : Prop)
    (h73388 : p3359 ∨ p3343)
    (h45994 : (¬ p2598) ∨ (¬ p3016) ∨ (¬ p3333) ∨ (¬ p3359))
    : (¬ p3333) ∨ p3343 ∨ (¬ p3016) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45994 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step95560 (p2553 p2588 p3333 p3422 p3584 p4331 p4624 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h73282 : p2588 ∨ p2553)
    (h51201 : (¬ p2588) ∨ (¬ p3333) ∨ (¬ p3584) ∨ (¬ p4331) ∨ (¬ p4624))
    : (¬ p4331) ∨ (¬ p3333) ∨ p3422 ∨ p2553 ∨ (¬ p4624) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4624 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h51201 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step95561 (p2563 p2850 p3333 p3343 p3359 p3684 p4110 : Prop)
    (h73388 : p3359 ∨ p3343)
    (h73516 : p4110 ∨ p2563)
    (h73442 : p3684 ∨ p2850)
    (h47694 : (¬ p3333) ∨ (¬ p3359) ∨ (¬ p3684) ∨ (¬ p4110))
    : (¬ p3333) ∨ p3343 ∨ p2563 ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47694 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step95562 (p2563 p2850 p3193 p3333 p3684 p4110 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73516 : p4110 ∨ p2563)
    (h59879 : (¬ p3193) ∨ (¬ p3333) ∨ (¬ p3684) ∨ (¬ p4110))
    : (¬ p3333) ∨ (¬ p3193) ∨ p2850 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h59879 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step95570 (p2264 p2459 p2573 p2807 p3333 p3362 p3414 p3422 p3553 p3584 p4332 p4348 p4789 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73410 : p3553 ∨ p2264)
    (h73392 : p3414 ∨ p2807)
    (h73426 : p3584 ∨ p3422)
    (h65001 : (¬ p2573) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3584) ∨ (¬ p4332) ∨ (¬ p4348) ∨ (¬ p4789))
    : p2459 ∨ p2264 ∨ (¬ p3333) ∨ (¬ p2573) ∨ (¬ p4332) ∨ (¬ p3362) ∨ p2807 ∨ (¬ p4789) ∨ p3422 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2264) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h65001 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step95577 (p2573 p2946 p2952 p3146 p3156 p3333 p3362 p3422 p3497 p3584 p3692 p4330 p4331 p4789 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h73400 : p3497 ∨ p3156)
    (h73448 : p3692 ∨ p3146)
    (h73330 : p2952 ∨ p2946)
    (h64954 : (¬ p2573) ∨ (¬ p2952) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3497) ∨ (¬ p3584) ∨ (¬ p3692) ∨ (¬ p4330) ∨ (¬ p4331) ∨ (¬ p4789))
    : (¬ p4331) ∨ p3422 ∨ (¬ p4789) ∨ p3156 ∨ (¬ p3362) ∨ p3146 ∨ (¬ p4330) ∨ (¬ p3333) ∨ p2946 ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h64954 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step95579 (p2696 p2753 p2761 p3333 p3365 p3367 p3645 p4032 p4243 p4322 p4638 p5052 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h63661 : p2753 ∨ (¬ p2761) ∨ (¬ p3333) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3645) ∨ (¬ p4032) ∨ (¬ p4243) ∨ (¬ p4322) ∨ (¬ p4638) ∨ (¬ p5052))
    : (¬ p3333) ∨ p2753 ∨ (¬ p5052) ∨ p2696 ∨ (¬ p3367) ∨ (¬ p2761) ∨ (¬ p4322) ∨ (¬ p4638) ∨ (¬ p4032) ∨ (¬ p3645) ∨ (¬ p4243) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2753) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5052 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4638 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63661 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u7))) (fun r9 => (False.elim (r9 u2)))))))))))))))))))))))

theorem step95584 (p3201 p3333 p3876 p4635 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h20241 : (¬ p3333) ∨ (¬ p3876) ∨ (¬ p4635))
    : (¬ p3333) ∨ (¬ p4635) ∨ p3201 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4635 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20241 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step95585 (p2761 p3201 p3276 p3333 p3876 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73486 : p3876 ∨ p3201)
    (h52784 : (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3876) ∨ (¬ p4381))
    : p2761 ∨ (¬ p3276) ∨ (¬ p3333) ∨ p3201 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h52784 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step95586 (p2449 p3201 p3333 p3876 p3947 p4327 p5182 p5299 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73494 : p3947 ∨ p2449)
    (h42343 : (¬ p3333) ∨ (¬ p3876) ∨ (¬ p3947) ∨ (¬ p4327) ∨ (¬ p5182) ∨ (¬ p5299))
    : (¬ p5299) ∨ (¬ p3333) ∨ (¬ p5182) ∨ p3201 ∨ (¬ p4327) ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5182 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4327 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h42343 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step95590 (p2230 p2589 p3201 p3333 p3389 p3876 p4953 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73284 : p2589 ∨ p2230)
    (h63772 : (¬ p2589) ∨ (¬ p3333) ∨ (¬ p3389) ∨ (¬ p3876) ∨ (¬ p4953))
    : p3201 ∨ (¬ p3333) ∨ (¬ p3389) ∨ (¬ p4953) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63772 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step95591 (p2459 p3333 p3641 p3874 p4348 p4438 p4695 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73484 : p3874 ∨ p3641)
    (h50001 : (¬ p3333) ∨ (¬ p3874) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p4695))
    : (¬ p3333) ∨ (¬ p4438) ∨ p2459 ∨ (¬ p4695) ∨ p3641 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50001 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step95597 (p3333 p3641 p3874 p4045 : Prop)
    (h73484 : p3874 ∨ p3641)
    (h20362 : (¬ p3333) ∨ (¬ p3874) ∨ (¬ p4045))
    : (¬ p3333) ∨ (¬ p4045) ∨ p3641 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20362 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step95598 (p3333 p3641 p3874 p4149 p4286 p4695 p5118 : Prop)
    (h73548 : p4286 ∨ p4149)
    (h73484 : p3874 ∨ p3641)
    (h65161 : (¬ p3333) ∨ (¬ p3874) ∨ (¬ p4286) ∨ (¬ p4695) ∨ (¬ p5118))
    : p4149 ∨ (¬ p3333) ∨ p3641 ∨ (¬ p4695) ∨ (¬ p5118) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4149) := (fun h => hn (Or.inl h));
    let u1 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4286 := (Or.elim h73548 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h65161 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step95600 (p2252 p2264 p2598 p2750 p2753 p2807 p3276 p3333 p3414 p3553 p5123 p5558 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h73392 : p3414 ∨ p2807)
    (h42614 : (¬ p2252) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p5123) ∨ (¬ p5558))
    : (¬ p3333) ∨ (¬ p5558) ∨ (¬ p2753) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p5123) ∨ p2264 ∨ (¬ p2252) ∨ p2807 ∨ (¬ p3276) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h42614 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u1)))))))))))))))))))))

theorem step95601 (p2156 p2187 p2363 p2608 p3333 p3367 p3646 p3989 p4332 p4347 p4524 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73436 : p3646 ∨ p2156)
    (h73502 : p3989 ∨ p2187)
    (h72962 : p4524)
    (h57940 : (¬ p2608) ∨ (¬ p3333) ∨ (¬ p3367) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4332) ∨ (¬ p4347) ∨ (¬ p4524))
    : p2363 ∨ (¬ p4332) ∨ (¬ p3333) ∨ p2156 ∨ (¬ p2608) ∨ p2187 ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p4524 := h72962;
    (Or.elim h57940 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u10)))))))))))))))))

theorem step95603 (p2839 p3333 p3367 p3583 p3698 p4953 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h41644 : (¬ p3333) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p4953))
    : (¬ p3333) ∨ p2839 ∨ (¬ p3367) ∨ (¬ p3698) ∨ (¬ p4953) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41644 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step95606 (p2651 p3136 p3146 p3276 p3333 p3661 p3692 p3969 p4315 p4343 p4790 p5600 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73550 : p4315 ∨ p3136)
    (h57590 : (¬ p2651) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3661) ∨ (¬ p3692) ∨ (¬ p3969) ∨ (¬ p4315) ∨ (¬ p4343) ∨ (¬ p4790) ∨ (¬ p5600))
    : (¬ p3969) ∨ (¬ p5600) ∨ (¬ p4343) ∨ (¬ p3333) ∨ (¬ p3276) ∨ (¬ p2651) ∨ (¬ p3661) ∨ p3146 ∨ (¬ p4790) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u11 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h57590 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u1)))))))))))))))))))))

theorem step95608 (p3193 p3333 p3379 p3422 p3452 p3584 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73426 : p3584 ∨ p3422)
    (h45522 : (¬ p3193) ∨ (¬ p3333) ∨ (¬ p3452) ∨ (¬ p3584))
    : (¬ p3193) ∨ (¬ p3333) ∨ p3379 ∨ p3422 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3193 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45522 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step95609 (p2230 p2331 p2363 p2668 p2850 p2963 p3324 p3333 p3362 p3684 p4332 p4347 p4789 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73386 : p3324 ∨ p2668)
    (h73338 : p2963 ∨ p2331)
    (h73442 : p3684 ∨ p2850)
    (h64702 : (¬ p2230) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3684) ∨ (¬ p4332) ∨ (¬ p4347) ∨ (¬ p4789))
    : (¬ p3333) ∨ p2363 ∨ (¬ p4332) ∨ (¬ p4789) ∨ p2668 ∨ (¬ p2230) ∨ (¬ p3362) ∨ p2331 ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h64702 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step95610 (p2331 p2363 p2668 p2963 p3201 p3324 p3333 p3362 p3389 p3876 p4332 p4347 p4789 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73338 : p2963 ∨ p2331)
    (h73486 : p3876 ∨ p3201)
    (h73386 : p3324 ∨ p2668)
    (h42635 : (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3876) ∨ (¬ p4332) ∨ (¬ p4347) ∨ (¬ p4789))
    : (¬ p3333) ∨ p2363 ∨ (¬ p3362) ∨ (¬ p4332) ∨ (¬ p3389) ∨ p2331 ∨ (¬ p4789) ∨ p3201 ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h42635 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step95612 (p2668 p3323 p3333 p3422 p3584 p4037 p4331 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73426 : p3584 ∨ p3422)
    (h44170 : (¬ p2668) ∨ (¬ p3333) ∨ (¬ p3584) ∨ (¬ p4037) ∨ (¬ p4331))
    : (¬ p4331) ∨ (¬ p3333) ∨ (¬ p2668) ∨ p3323 ∨ p3422 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h44170 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step95613 (p2295 p3323 p3333 p3641 p3874 p4037 p4331 : Prop)
    (h73484 : p3874 ∨ p3641)
    (h73508 : p4037 ∨ p3323)
    (h59341 : (¬ p2295) ∨ (¬ p3333) ∨ (¬ p3874) ∨ (¬ p4037) ∨ (¬ p4331))
    : (¬ p2295) ∨ (¬ p3333) ∨ (¬ p4331) ∨ p3641 ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h59341 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step95614 (p2459 p2608 p2881 p3051 p3333 p3367 p3556 p3570 p4332 p4348 p4524 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73418 : p3570 ∨ p2881)
    (h72962 : p4524)
    (h73414 : p3556 ∨ p3051)
    (h52051 : (¬ p2608) ∨ (¬ p3333) ∨ (¬ p3367) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4332) ∨ (¬ p4348) ∨ (¬ p4524))
    : p2459 ∨ p2881 ∨ p3051 ∨ (¬ p2608) ∨ (¬ p4332) ∨ (¬ p3367) ∨ (¬ p3333) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4524 := h72962;
    let u10 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52051 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u9)))))))))))))))))

theorem step95618 (p2911 p3201 p3333 p3346 p3644 p3876 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73434 : p3644 ∨ p2911)
    (h43225 : (¬ p3333) ∨ (¬ p3346) ∨ (¬ p3644) ∨ (¬ p3876))
    : (¬ p3333) ∨ (¬ p3346) ∨ p3201 ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43225 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step95620 (p3266 p3276 p3333 p3422 p3584 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73426 : p3584 ∨ p3422)
    (h45667 : (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3584) ∨ (¬ p4444))
    : (¬ p3333) ∨ p3266 ∨ (¬ p3276) ∨ p3422 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45667 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step95623 (p2396 p3201 p3333 p3876 p4107 p4451 p4712 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73486 : p3876 ∨ p3201)
    (h49405 : (¬ p3333) ∨ (¬ p3876) ∨ (¬ p4107) ∨ (¬ p4451) ∨ (¬ p4712))
    : (¬ p4451) ∨ (¬ p3333) ∨ p2396 ∨ (¬ p4712) ∨ p3201 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4451 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49405 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step95625 (p2252 p2331 p2598 p2668 p2750 p2753 p2963 p3276 p3324 p3333 p5123 p5580 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73386 : p3324 ∨ p2668)
    (h42619 : (¬ p2252) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2963) ∨ (¬ p3276) ∨ (¬ p3324) ∨ (¬ p3333) ∨ (¬ p5123) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p2753) ∨ p2331 ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p2598) ∨ (¬ p2750) ∨ p2668 ∨ (¬ p5123) ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h42619 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step95626 (p2241 p2750 p2753 p3093 p3201 p3323 p3333 p3362 p3389 p3591 p3876 p4037 p4319 p5322 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73508 : p4037 ∨ p3323)
    (h73486 : p3876 ∨ p3201)
    (h64851 : (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3591) ∨ (¬ p3876) ∨ (¬ p4037) ∨ (¬ p4319) ∨ (¬ p5322))
    : p3093 ∨ (¬ p2241) ∨ (¬ p3362) ∨ (¬ p2753) ∨ (¬ p4319) ∨ (¬ p2750) ∨ p3323 ∨ (¬ p3389) ∨ (¬ p3333) ∨ (¬ p5322) ∨ p3201 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h64851 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u13))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u4))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step95627 (p2230 p2264 p2459 p2807 p2850 p3333 p3362 p3414 p3553 p3684 p4332 p4348 p4789 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73392 : p3414 ∨ p2807)
    (h73410 : p3553 ∨ p2264)
    (h73562 : p4348 ∨ p2459)
    (h64604 : (¬ p2230) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3684) ∨ (¬ p4332) ∨ (¬ p4348) ∨ (¬ p4789))
    : (¬ p3333) ∨ (¬ p4332) ∨ (¬ p4789) ∨ (¬ p3362) ∨ p2850 ∨ p2807 ∨ p2264 ∨ p2459 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64604 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step95630 (p2598 p2761 p3276 p3333 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h46495 : (¬ p2598) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p4381))
    : (¬ p3333) ∨ p2761 ∨ (¬ p3276) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46495 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step95632 (p2850 p3333 p3684 p3767 p4322 p5182 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h48422 : (¬ p3333) ∨ (¬ p3684) ∨ (¬ p3767) ∨ (¬ p4322) ∨ (¬ p5182))
    : (¬ p3767) ∨ (¬ p4322) ∨ p2850 ∨ (¬ p3333) ∨ (¬ p5182) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3767 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5182 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48422 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step95634 (p2252 p2573 p2750 p2753 p3266 p3286 p3292 p3333 p3362 p3422 p3584 p3950 p4331 p4623 p5284 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h73426 : p3584 ∨ p3422)
    (h64922 : (¬ p2252) ∨ (¬ p2573) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3266) ∨ (¬ p3292) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3584) ∨ (¬ p3950) ∨ (¬ p4331) ∨ (¬ p4623) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p3266) ∨ (¬ p3950) ∨ (¬ p2750) ∨ (¬ p3362) ∨ (¬ p3333) ∨ (¬ p2573) ∨ (¬ p2753) ∨ (¬ p4331) ∨ (¬ p4623) ∨ p3286 ∨ p3422 ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4623 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    let u14 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    (Or.elim h64922 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u14))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u8))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u9))) (fun r11 => (False.elim (r11 u0)))))))))))))))))))))))))))

theorem step95639 (p2651 p2957 p3051 p3136 p3276 p3333 p3556 p4315 p4343 p4790 p4831 p5660 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73414 : p3556 ∨ p3051)
    (h64376 : (¬ p2651) ∨ (¬ p2957) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3556) ∨ (¬ p4315) ∨ (¬ p4343) ∨ (¬ p4790) ∨ (¬ p4831) ∨ (¬ p5660))
    : p3136 ∨ (¬ p3333) ∨ p3051 ∨ (¬ p4343) ∨ (¬ p4790) ∨ (¬ p3276) ∨ (¬ p5660) ∨ (¬ p4831) ∨ (¬ p2651) ∨ (¬ p2957) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h64376 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step95642 (p2850 p3276 p3333 p3461 p3684 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73442 : p3684 ∨ p2850)
    (h56805 : (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3684) ∨ (¬ p4191))
    : (¬ p3276) ∨ p3461 ∨ (¬ p3333) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56805 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step95643 (p2177 p2295 p2331 p3333 p3346 p3641 p3874 p3905 p4438 p4786 : Prop)
    (h73484 : p3874 ∨ p3641)
    (h64271 : (¬ p2177) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3333) ∨ (¬ p3346) ∨ (¬ p3874) ∨ (¬ p3905) ∨ (¬ p4438) ∨ (¬ p4786))
    : (¬ p3333) ∨ (¬ p3346) ∨ (¬ p2295) ∨ (¬ p4786) ∨ (¬ p4438) ∨ (¬ p3905) ∨ (¬ p2331) ∨ p3641 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64271 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step95648 (p2139 p2156 p2274 p2396 p2696 p3005 p3256 p3365 p3877 p3950 p4118 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h73488 : p3877 ∨ p3005)
    (h73390 : p3365 ∨ p2696)
    (h41982 : (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118))
    : (¬ p2396) ∨ p3256 ∨ (¬ p2274) ∨ (¬ p3950) ∨ p3005 ∨ (¬ p2139) ∨ (¬ p2156) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h41982 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u8)))))))))))))))))

theorem step95649 (p2139 p2696 p2761 p3005 p3051 p3246 p3365 p3877 p5123 p5600 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h73488 : p3877 ∨ p3005)
    (h41981 : (¬ p2139) ∨ (¬ p2761) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p5123) ∨ (¬ p5600))
    : (¬ p5600) ∨ (¬ p2761) ∨ p2696 ∨ (¬ p2139) ∨ (¬ p3051) ∨ p3005 ∨ (¬ p3246) ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5600 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41981 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step95650 (p2139 p2156 p2264 p2427 p2563 p2717 p3425 p3659 p4110 p4362 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h73516 : p4110 ∨ p2563)
    (h64695 : (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2264) ∨ (¬ p2427) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4110) ∨ (¬ p4362))
    : p2717 ∨ (¬ p2427) ∨ (¬ p2264) ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p3425) ∨ (¬ p4362) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64695 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step95651 (p2139 p2156 p2284 p2598 p2911 p3055 p3156 p3201 p3644 p3876 p3952 p4133 p4441 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73434 : p3644 ∨ p2911)
    (h73350 : p3055 ∨ p2598)
    (h73486 : p3876 ∨ p3201)
    (h61509 : (¬ p2139) ∨ (¬ p2156) ∨ (¬ p3055) ∨ (¬ p3156) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p3952) ∨ (¬ p4133) ∨ (¬ p4441))
    : (¬ p3156) ∨ p2284 ∨ (¬ p4441) ∨ p2911 ∨ p2598 ∨ (¬ p2156) ∨ (¬ p4133) ∨ (¬ p2139) ∨ p3201 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h61509 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step95653 (p2139 p2220 p2459 p2573 p2579 p3256 p3422 p3641 p3874 p3905 p4312 p4348 p4438 : Prop)
    (h73484 : p3874 ∨ p3641)
    (h73274 : p2579 ∨ p2573)
    (h73562 : p4348 ∨ p2459)
    (h63853 : (¬ p2139) ∨ (¬ p2220) ∨ (¬ p2579) ∨ (¬ p3256) ∨ (¬ p3422) ∨ (¬ p3874) ∨ (¬ p3905) ∨ (¬ p4312) ∨ (¬ p4348) ∨ (¬ p4438))
    : (¬ p4312) ∨ p3641 ∨ p2573 ∨ (¬ p3905) ∨ (¬ p2139) ∨ p2459 ∨ (¬ p4438) ∨ (¬ p3256) ∨ (¬ p3422) ∨ (¬ p2220) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4312 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h63853 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step95654 (p4524 p4984 p5210 : Prop)
    (h72962 : p4524)
    (h24838 : (¬ p4524) ∨ (¬ p4984) ∨ p5210)
    : p5210 ∨ (¬ p4984) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5210) := (fun h => hn (Or.inl h));
    let u1 : p4984 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4524 := h72962;
    (Or.elim h24838 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step95661 (p2341 p2881 p2957 p3136 p3246 p3551 p3690 p4315 p4984 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73408 : p3551 ∨ p2341)
    (h73550 : p4315 ∨ p3136)
    (h55869 : (¬ p2881) ∨ (¬ p2957) ∨ (¬ p3551) ∨ (¬ p3690) ∨ (¬ p4315) ∨ (¬ p4984))
    : p3246 ∨ p2341 ∨ p3136 ∨ (¬ p2957) ∨ (¬ p4984) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h55869 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step95673 (p2156 p2284 p2396 p3516 p3821 p3952 p4984 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73496 : p3952 ∨ p2284)
    (h45101 : (¬ p2156) ∨ (¬ p2396) ∨ (¬ p3821) ∨ (¬ p3952) ∨ (¬ p4984))
    : p3516 ∨ (¬ p2396) ∨ (¬ p2156) ∨ (¬ p4984) ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45101 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step95678 (p2156 p2341 p2881 p3551 p4555 p4984 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h64003 : (¬ p2156) ∨ (¬ p2881) ∨ (¬ p3551) ∨ (¬ p4555) ∨ (¬ p4984))
    : p2341 ∨ (¬ p2881) ∨ (¬ p2156) ∨ (¬ p4984) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h64003 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step95679 (p2341 p2427 p2881 p3551 p4533 p4984 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h63657 : (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3551) ∨ (¬ p4533) ∨ (¬ p4984))
    : p2341 ∨ (¬ p2881) ∨ (¬ p4984) ∨ (¬ p2427) ∨ (¬ p4533) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h63657 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step95680 (p2341 p2761 p2957 p2992 p3266 p3551 p3657 p3662 p4381 p4984 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73408 : p3551 ∨ p2341)
    (h73440 : p3662 ∨ p2992)
    (h60294 : (¬ p2957) ∨ (¬ p3266) ∨ (¬ p3551) ∨ (¬ p3657) ∨ (¬ p3662) ∨ (¬ p4381) ∨ (¬ p4984))
    : p2761 ∨ (¬ p3266) ∨ (¬ p2957) ∨ p2341 ∨ (¬ p3657) ∨ p2992 ∨ (¬ p4984) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h60294 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step95683 (p2220 p2437 p3016 p3096 p3574 p3575 p4509 p4984 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h50328 : (¬ p2220) ∨ (¬ p2437) ∨ (¬ p3096) ∨ (¬ p3574) ∨ (¬ p3575) ∨ (¬ p4509) ∨ (¬ p4984))
    : (¬ p2437) ∨ p3016 ∨ (¬ p3096) ∨ (¬ p4509) ∨ (¬ p4984) ∨ (¬ p3575) ∨ (¬ p2220) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h50328 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step95685 (p2427 p3246 p3516 p3821 p4533 p4984 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h64482 : (¬ p2427) ∨ (¬ p3246) ∨ (¬ p3821) ∨ (¬ p4533) ∨ (¬ p4984))
    : (¬ p3246) ∨ p3516 ∨ (¬ p4984) ∨ (¬ p2427) ∨ (¬ p4533) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3516) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h64482 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step95686 (p2140 p2870 p3246 p3516 p3821 p4984 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h41369 : (¬ p2140) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3821) ∨ (¬ p4984))
    : (¬ p3246) ∨ p3516 ∨ (¬ p2140) ∨ (¬ p2870) ∨ (¬ p4984) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3516) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41369 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step95687 (p2156 p2177 p2341 p2563 p3551 p4110 p4984 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73516 : p4110 ∨ p2563)
    (h44580 : (¬ p2156) ∨ (¬ p2177) ∨ (¬ p3551) ∨ (¬ p4110) ∨ (¬ p4984))
    : p2341 ∨ (¬ p2177) ∨ (¬ p4984) ∨ (¬ p2156) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h44580 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step95688 (p2341 p2563 p2881 p3551 p3872 p4533 p4984 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h56104 : (¬ p2563) ∨ (¬ p2881) ∨ (¬ p3551) ∨ (¬ p3872) ∨ (¬ p4533) ∨ (¬ p4984))
    : p2341 ∨ (¬ p2881) ∨ (¬ p3872) ∨ (¬ p4533) ∨ (¬ p2563) ∨ (¬ p4984) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h56104 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step95689 (p2177 p2437 p2440 p2542 p3527 p3543 p3548 p3742 p4279 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h73452 : p3742 ∨ p2437)
    (h73270 : p2542 ∨ p2440)
    (h61253 : (¬ p2177) ∨ (¬ p2542) ∨ (¬ p3543) ∨ (¬ p3548) ∨ (¬ p3742) ∨ (¬ p4279))
    : (¬ p3543) ∨ p3527 ∨ p2437 ∨ (¬ p2177) ∨ p2440 ∨ (¬ p4279) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3543 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3527) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4279 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h61253 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step95691 (p3516 p3543 p3631 p3817 p3821 : Prop)
    (h73469 : (¬ p3516) ∨ (¬ p3821))
    (h73468 : p3817 ∨ p3631)
    (h25184 : (¬ p3543) ∨ (¬ p3817) ∨ p3821)
    : (¬ p3543) ∨ (¬ p3516) ∨ p3631 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3543 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3821) := (Or.elim h73469 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u4 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h25184 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (u3 r1)))))))

theorem step95699 (p2318 p2553 p2588 p2717 p3426 p3527 p3543 p3548 p5225 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h73282 : p2588 ∨ p2553)
    (h42095 : (¬ p2318) ∨ (¬ p2588) ∨ (¬ p2717) ∨ (¬ p3426) ∨ (¬ p3543) ∨ (¬ p3548) ∨ (¬ p5225))
    : (¬ p3543) ∨ (¬ p2717) ∨ (¬ p2318) ∨ p3527 ∨ p2553 ∨ (¬ p5225) ∨ (¬ p3426) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3543 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2318 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5225 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42095 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step95700 (p2563 p2779 p2829 p2839 p3583 p4110 p4356 p4885 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h73424 : p3583 ∨ p2839)
    (h55624 : (¬ p2779) ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p4110) ∨ (¬ p4356) ∨ (¬ p4885))
    : (¬ p2829) ∨ (¬ p4356) ∨ p2563 ∨ p2839 ∨ (¬ p2779) ∨ (¬ p4885) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2779 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55624 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step95704 (p2274 p2307 p2598 p2696 p2779 p3055 p3097 p3125 p3985 p5160 p5325 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73350 : p3055 ∨ p2598)
    (h67350 : (¬ p2779) ∨ (¬ p2696) ∨ (¬ p5160) ∨ (¬ p3985) ∨ (¬ p3055) ∨ (¬ p5325) ∨ (¬ p2307) ∨ (¬ p3097) ∨ (¬ p3125))
    : (¬ p2779) ∨ (¬ p5160) ∨ (¬ p2696) ∨ p2274 ∨ (¬ p3985) ∨ (¬ p2307) ∨ (¬ p5325) ∨ (¬ p3125) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2779 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3985 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h67350 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step95706 (p2598 p2696 p2761 p2779 p3055 p3461 p3654 p3985 p4381 p4641 p5160 : Prop)
    (h73350 : p3055 ∨ p2598)
    (h73574 : p4381 ∨ p2761)
    (h67351 : (¬ p2779) ∨ (¬ p2696) ∨ (¬ p3654) ∨ (¬ p3985) ∨ (¬ p5160) ∨ (¬ p4641) ∨ (¬ p3461) ∨ (¬ p4381) ∨ (¬ p3055))
    : (¬ p5160) ∨ (¬ p3985) ∨ (¬ p2779) ∨ (¬ p3654) ∨ (¬ p2696) ∨ (¬ p3461) ∨ p2598 ∨ p2761 ∨ (¬ p4641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5160 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3985 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2779 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u10 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h67351 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step95707 (p2307 p2737 p2779 p3309 p3549 p3953 p4842 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h42299 : (¬ p2307) ∨ (¬ p2737) ∨ (¬ p2779) ∨ (¬ p3549) ∨ (¬ p3953) ∨ (¬ p4842))
    : (¬ p2779) ∨ (¬ p3953) ∨ p3309 ∨ (¬ p4842) ∨ (¬ p2737) ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2779 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42299 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step95711 (p2737 p2743 p2779 p2829 p3461 p3654 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h45570 : (¬ p2743) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (¬ p3461) ∨ (¬ p3654))
    : (¬ p2779) ∨ p2737 ∨ (¬ p2829) ∨ (¬ p3654) ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2779 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45570 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step95713 (p2383 p2387 p2779 p2819 p4358 : Prop)
    (h73245 : (¬ p2383) ∨ (¬ p2387))
    (h73564 : p4358 ∨ p2819)
    (h19665 : p2387 ∨ (¬ p2779) ∨ (¬ p4358))
    : (¬ p2383) ∨ (¬ p2779) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2779 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2387) := (Or.elim h73245 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h19665 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step95716 (p2088 p2363 p2696 p2748 p2779 p2829 p2992 p3156 p3365 p3497 p3662 p4114 p4134 p4347 p4734 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73440 : p3662 ∨ p2992)
    (h72735 : p4734)
    (h73400 : p3497 ∨ p3156)
    (h73390 : p3365 ∨ p2696)
    (h51453 : (¬ p2088) ∨ (¬ p2748) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (¬ p3365) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p4114) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p4734))
    : (¬ p4114) ∨ p2363 ∨ (¬ p4134) ∨ p2992 ∨ (¬ p2829) ∨ (¬ p2748) ∨ (¬ p2088) ∨ p3156 ∨ p2696 ∨ (¬ p2779) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4114 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2779 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p4734 := h72735;
    let u13 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u14 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h51453 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u14))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (False.elim (r9 u12)))))))))))))))))))))))

theorem step95718 (p2307 p2313 p2779 p2819 p3325 p4358 : Prop)
    (h73237 : (¬ p2307) ∨ (¬ p2313))
    (h73564 : p4358 ∨ p2819)
    (h21485 : p2313 ∨ (¬ p2779) ∨ (¬ p3325) ∨ (¬ p4358))
    : (¬ p3325) ∨ (¬ p2307) ∨ (¬ p2779) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3325 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2779 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2313) := (Or.elim h73237 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h21485 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step95719 (p2307 p2553 p2588 p2779 p2829 p3367 p3585 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73428 : p3585 ∨ p3367)
    (h57450 : (¬ p2307) ∨ (¬ p2588) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (¬ p3585))
    : (¬ p2779) ∨ (¬ p2829) ∨ p2553 ∨ (¬ p2307) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2779 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h57450 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step95726 (p2274 p2307 p2737 p2743 p2779 p2829 p3097 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73298 : p2743 ∨ p2737)
    (h48882 : (¬ p2307) ∨ (¬ p2743) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (¬ p3097))
    : (¬ p2779) ∨ p2274 ∨ p2737 ∨ (¬ p2307) ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2779 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48882 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step95727 (p2122 p2307 p2779 p3822 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h5636 : (¬ p2307) ∨ (¬ p2779) ∨ (¬ p3822))
    : (¬ p2779) ∨ (¬ p2307) ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2779 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h5636 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u3)))))))

theorem step95729 (p2177 p2386 p2553 p2779 p2829 p3367 p3585 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h46297 : (¬ p2177) ∨ (¬ p2386) ∨ (¬ p2553) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (¬ p3585))
    : (¬ p2779) ∨ (¬ p2829) ∨ (¬ p2177) ∨ (¬ p2386) ∨ (¬ p2553) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2779 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h46297 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step95732 (p2177 p2307 p2696 p2727 p2748 p2779 p2829 p3083 p3365 p4111 p4256 p4438 p4734 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h72735 : p4734)
    (h73542 : p4256 ∨ p3083)
    (h73518 : p4111 ∨ p2727)
    (h62444 : (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2748) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (¬ p3365) ∨ (¬ p4111) ∨ (¬ p4256) ∨ (¬ p4438) ∨ (¬ p4734))
    : (¬ p2748) ∨ p2696 ∨ (¬ p4438) ∨ p3083 ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2829) ∨ p2727 ∨ (¬ p2779) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2748 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2779 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4734 := h72735;
    let u11 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h62444 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (r8 u10)))))))))))))))))))))

theorem step95733 (p2933 p3389 p3426 p3434 p3540 p3631 p3817 p4375 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h73468 : p3817 ∨ p3631)
    (h72098 : (¬ p3817) ∨ (¬ p3434) ∨ (¬ p2933) ∨ (¬ p3426) ∨ (¬ p3540) ∨ (¬ p4375))
    : (¬ p2933) ∨ (¬ p3426) ∨ (¬ p4375) ∨ p3389 ∨ (¬ p3434) ∨ p3631 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2933 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h72098 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step95739 (p3166 p3170 p3175 : Prop)
    (h73357 : p3166 ∨ (¬ p3175))
    (h4468 : p3170 ∨ p3175)
    : p3170 ∨ p3166 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3170) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr h));
    let u2 : (¬ p3175) := (Or.elim h73357 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h4468 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95743 (p2449 p3434 p3947 p4777 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h28846 : (¬ p3434) ∨ (¬ p3947) ∨ (¬ p4777))
    : (¬ p3434) ∨ (¬ p4777) ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4777 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h28846 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step95745 (p2264 p2717 p3553 p3659 p4777 : Prop)
    (h73437 : (¬ p2717) ∨ (¬ p3659))
    (h73410 : p3553 ∨ p2264)
    (h35465 : (¬ p3553) ∨ p3659 ∨ (¬ p4777))
    : (¬ p2717) ∨ (¬ p4777) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4777 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3659) := (Or.elim h73437 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h35465 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step95750 (p2417 p2449 p2737 p3366 p3425 p3947 p4777 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h57532 : (¬ p2417) ∨ (¬ p2737) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3947) ∨ (¬ p4777))
    : p2449 ∨ (¬ p3425) ∨ (¬ p2417) ∨ (¬ p4777) ∨ (¬ p2737) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4777 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h57532 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step95751 (p2651 p2657 p2807 p2922 p2928 p3658 p4777 p4811 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73320 : p2928 ∨ p2922)
    (h53843 : (¬ p2657) ∨ (¬ p2807) ∨ (¬ p2928) ∨ (¬ p3658) ∨ (¬ p4777) ∨ (¬ p4811))
    : (¬ p3658) ∨ p2651 ∨ p2922 ∨ (¬ p4777) ∨ (¬ p4811) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3658 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4777 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h53843 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step95755 (p2230 p2264 p2427 p2608 p3246 p3399 p3519 p3553 p4366 p4376 p4424 p4668 p4777 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73410 : p3553 ∨ p2264)
    (h51147 : (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p3246) ∨ (¬ p3519) ∨ (¬ p3553) ∨ (¬ p4366) ∨ (¬ p4376) ∨ (¬ p4424) ∨ (¬ p4668) ∨ (¬ p4777))
    : (¬ p3246) ∨ p3399 ∨ (¬ p4668) ∨ (¬ p3519) ∨ (¬ p2608) ∨ p2264 ∨ (¬ p2230) ∨ (¬ p4424) ∨ (¬ p2427) ∨ (¬ p4777) ∨ (¬ p4376) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4424 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4777 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h51147 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step95756 (p2373 p2995 p3880 p4019 p4705 p4777 p4805 p5568 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h62107 : (¬ p2995) ∨ (¬ p3880) ∨ (¬ p4019) ∨ (¬ p4705) ∨ (¬ p4777) ∨ (¬ p4805) ∨ (¬ p5568))
    : (¬ p4019) ∨ (¬ p5568) ∨ (¬ p2995) ∨ (¬ p4777) ∨ (¬ p4805) ∨ p2373 ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4019 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4777 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4805 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h62107 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u1)))))))))))))))

theorem step95767 (p2363 p3449 p3830 p3860 p4347 p4352 p4998 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h73560 : p4347 ∨ p2363)
    (h42002 : (¬ p3830) ∨ (¬ p3860) ∨ (¬ p4347) ∨ (¬ p4352) ∨ (¬ p4998))
    : (¬ p4352) ∨ p3449 ∨ (¬ p3830) ∨ (¬ p4998) ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42002 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step95770 (p3146 p3449 p3692 p3830 p3860 p4352 p4498 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73482 : p3860 ∨ p3449)
    (h48209 : (¬ p3692) ∨ (¬ p3830) ∨ (¬ p3860) ∨ (¬ p4352) ∨ (¬ p4498))
    : p3146 ∨ (¬ p4352) ∨ p3449 ∨ (¬ p4498) ∨ (¬ p3830) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p4352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4498 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48209 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step95771 (p2166 p2946 p3166 p3172 p4312 p4960 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h41561 : (¬ p2166) ∨ (¬ p2946) ∨ (¬ p3172) ∨ (¬ p4312) ∨ (¬ p4960))
    : (¬ p4312) ∨ p3166 ∨ (¬ p2946) ∨ (¬ p4960) ∨ (¬ p2166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4312 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41561 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step95772 (p2156 p2166 p2220 p2284 p3952 p4120 p4960 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h73496 : p3952 ∨ p2284)
    (h42348 : (¬ p2156) ∨ (¬ p2166) ∨ (¬ p3952) ∨ (¬ p4120) ∨ (¬ p4960))
    : p2220 ∨ p2284 ∨ (¬ p2156) ∨ (¬ p2166) ∨ (¬ p4960) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2220) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42348 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step95773 (p2210 p2284 p3093 p3555 p3952 p4516 p4960 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73496 : p3952 ∨ p2284)
    (h42193 : (¬ p3093) ∨ (¬ p3555) ∨ (¬ p3952) ∨ (¬ p4516) ∨ (¬ p4960))
    : (¬ p3093) ∨ p2210 ∨ (¬ p4960) ∨ p2284 ∨ (¬ p4516) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3093 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42193 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step95776 (p3434 p3516 p3577 p4324 : Prop)
    (h73556 : p4324 ∨ p3434)
    (h34455 : (¬ p3516) ∨ (¬ p3577) ∨ (¬ p4324))
    : (¬ p3577) ∨ (¬ p3516) ∨ p3434 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3577 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h34455 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u3)))))))

theorem step95778 (p2717 p3577 p3659 p4403 p4590 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h18242 : (¬ p3577) ∨ (¬ p3659) ∨ (¬ p4403) ∨ (¬ p4590))
    : (¬ p3577) ∨ (¬ p4590) ∨ (¬ p4403) ∨ p2717 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3577 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4403 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h18242 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step95779 (p2341 p2737 p3527 p3548 p3577 p4400 p4778 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h48014 : (¬ p2341) ∨ (¬ p2737) ∨ (¬ p3548) ∨ (¬ p3577) ∨ (¬ p4400) ∨ (¬ p4778))
    : (¬ p3577) ∨ (¬ p4400) ∨ p3527 ∨ (¬ p2341) ∨ (¬ p4778) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3577 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4400 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48014 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step95789 (p2177 p2299 p2341 p2707 p3367 p3577 p3585 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h73428 : p3585 ∨ p3367)
    (h46281 : (¬ p2299) ∨ (¬ p2341) ∨ (¬ p2707) ∨ (¬ p3577) ∨ (¬ p3585))
    : (¬ p2341) ∨ (¬ p2707) ∨ (¬ p3577) ∨ p2177 ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46281 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step95791 (p2860 p4428 p5935 : Prop)
    (h74253 : p2860 ∨ (¬ p5935))
    (h12593 : p4428 ∨ p5935)
    : p4428 ∨ p2860 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4428) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2860) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5935) := (Or.elim h74253 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12593 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95792 (p2860 p4193 p5935 : Prop)
    (h74253 : p2860 ∨ (¬ p5935))
    (h12595 : p4193 ∨ p5935)
    : p4193 ∨ p2860 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4193) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2860) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5935) := (Or.elim h74253 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12595 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95794 (p2860 p4889 p5935 : Prop)
    (h74253 : p2860 ∨ (¬ p5935))
    (h12597 : p4889 ∨ p5935)
    : p4889 ∨ p2860 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4889) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2860) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5935) := (Or.elim h74253 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12597 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95796 (p2608 p2829 p3379 p3452 p3590 p5224 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h51425 : (¬ p2608) ∨ (¬ p2829) ∨ (¬ p3452) ∨ (¬ p3590) ∨ (¬ p5224))
    : p3379 ∨ (¬ p2608) ∨ (¬ p2829) ∨ (¬ p3590) ∨ (¬ p5224) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5224 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h51425 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step95798 (p2103 p2177 p2299 p2707 p3537 p3588 p4403 p4477 : Prop)
    (h73430 : p3588 ∨ p2707)
    (h73234 : p2299 ∨ p2177)
    (h64020 : (¬ p2103) ∨ (¬ p2299) ∨ (¬ p3537) ∨ (¬ p3588) ∨ (¬ p4403) ∨ (¬ p4477))
    : (¬ p4403) ∨ (¬ p4477) ∨ p2707 ∨ p2177 ∨ (¬ p3537) ∨ (¬ p2103) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4403 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2103 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3588 := (Or.elim h73430 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h64020 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step95799 (p2341 p2459 p2528 p3551 p3875 p4348 p5199 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73562 : p4348 ∨ p2459)
    (h60532 : (¬ p2528) ∨ (¬ p3551) ∨ (¬ p3875) ∨ (¬ p4348) ∨ (¬ p5199))
    : p2341 ∨ (¬ p3875) ∨ p2459 ∨ (¬ p2528) ∨ (¬ p5199) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p3875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5199 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h60532 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step95800 (p2449 p2651 p3516 p3821 p4650 p4849 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h41885 : (¬ p2449) ∨ (¬ p2651) ∨ (¬ p3821) ∨ (¬ p4650) ∨ (¬ p4849))
    : (¬ p2449) ∨ p3516 ∨ (¬ p2651) ∨ (¬ p4650) ∨ (¬ p4849) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3516) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4849 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41885 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step95809 (p2341 p2651 p2727 p2911 p3551 p4111 p4849 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73408 : p3551 ∨ p2341)
    (h48282 : (¬ p2651) ∨ (¬ p2911) ∨ (¬ p3551) ∨ (¬ p4111) ∨ (¬ p4849))
    : p2727 ∨ (¬ p4849) ∨ p2341 ∨ (¬ p2911) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p4849 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48282 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step95818 (p2249 p2449 p2996 p3027 p3516 p3821 p4849 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73340 : p3027 ∨ p2996)
    (h51858 : (¬ p2249) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3821) ∨ (¬ p4849))
    : p3516 ∨ p2996 ∨ (¬ p4849) ∨ (¬ p2449) ∨ (¬ p2249) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4849 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h51858 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step95827 (p3461 p3506 p4190 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h6275 : (¬ p3506) ∨ (¬ p4190) ∨ (¬ p4191))
    : (¬ p3506) ∨ p3461 ∨ (¬ p4190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h6275 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step95832 (p2685 p3246 p3572 p3690 p3755 p4362 p4660 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h73446 : p3690 ∨ p3246)
    (h42417 : (¬ p3572) ∨ (¬ p3690) ∨ (¬ p3755) ∨ (¬ p4362) ∨ (¬ p4660))
    : (¬ p4660) ∨ (¬ p3755) ∨ (¬ p4362) ∨ p2685 ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4660 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42417 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step95834 (p2396 p2685 p3572 p3755 p4107 p4361 p4660 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73420 : p3572 ∨ p2685)
    (h51079 : (¬ p3572) ∨ (¬ p3755) ∨ (¬ p4107) ∨ (¬ p4361) ∨ (¬ p4660))
    : (¬ p3755) ∨ (¬ p4660) ∨ p2396 ∨ (¬ p4361) ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51079 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step95838 (p2363 p3609 p4326 p4340 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h19869 : (¬ p2363) ∨ (¬ p4326) ∨ (¬ p4340))
    : p3609 ∨ (¬ p4326) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p4326 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h19869 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step95842 (p2437 p3246 p3343 p3690 p3742 p4647 p5182 p5299 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73446 : p3690 ∨ p3246)
    (h58644 : (¬ p3343) ∨ (¬ p3690) ∨ (¬ p3742) ∨ (¬ p4647) ∨ (¬ p5182) ∨ (¬ p5299))
    : (¬ p3343) ∨ (¬ p5182) ∨ (¬ p4647) ∨ (¬ p5299) ∨ p2437 ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5182 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5299 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u7 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h58644 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step95843 (p2295 p3426 p3568 p4253 p4260 p4846 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h42497 : (¬ p3426) ∨ (¬ p3568) ∨ (¬ p4253) ∨ (¬ p4260) ∨ (¬ p4846))
    : (¬ p4253) ∨ (¬ p4260) ∨ (¬ p3426) ∨ p2295 ∨ (¬ p4846) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4253 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4846 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42497 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step95844 (p3323 p3461 p3670 p4037 p4191 p4231 p4846 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73508 : p4037 ∨ p3323)
    (h41430 : (¬ p3670) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4231) ∨ (¬ p4846))
    : (¬ p3670) ∨ (¬ p4231) ∨ p3461 ∨ (¬ p4846) ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3670 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4231 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4846 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41430 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step95845 (p2245 p2807 p3037 p3399 p3414 p4366 : Prop)
    (h73392 : p3414 ∨ p2807)
    (h73569 : (¬ p3399) ∨ (¬ p4366))
    (h30746 : (¬ p2245) ∨ (¬ p3037) ∨ (¬ p3414) ∨ p4366)
    : (¬ p3037) ∨ (¬ p2245) ∨ p2807 ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3037 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : (¬ p4366) := (Or.elim h73569 (fun q0 => (False.elim (q0 u3))) (fun r0 => r0));
    (Or.elim h30746 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (u5 r2)))))))))

theorem step95846 (p2449 p3037 p3631 p3817 : Prop)
    (h73468 : p3817 ∨ p3631)
    (h5631 : (¬ p2449) ∨ (¬ p3037) ∨ (¬ p3817))
    : p3631 ∨ (¬ p3037) ∨ (¬ p2449) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p3037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h5631 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step95848 (p2264 p3037 p3527 p3548 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h5199 : (¬ p2264) ∨ (¬ p3037) ∨ (¬ p3548))
    : p3527 ∨ (¬ p3037) ∨ (¬ p2264) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p3037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h5199 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step95856 (p2449 p3037 p3527 p3548 p3657 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h25818 : (¬ p2449) ∨ (¬ p3037) ∨ (¬ p3548) ∨ (¬ p3657))
    : (¬ p3037) ∨ (¬ p2449) ∨ (¬ p3657) ∨ p3527 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3037 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h25818 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step95859 (p2156 p2249 p2459 p2807 p2951 p2992 p3037 p3125 p3414 p3527 p3548 p4330 p4348 : Prop)
    (h73392 : p3414 ∨ p2807)
    (h73404 : p3548 ∨ p3527)
    (h73562 : p4348 ∨ p2459)
    (h62582 : (¬ p2156) ∨ (¬ p2249) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3037) ∨ (¬ p3125) ∨ (¬ p3414) ∨ (¬ p3548) ∨ (¬ p4330) ∨ (¬ p4348))
    : (¬ p3125) ∨ (¬ p2992) ∨ (¬ p3037) ∨ p2807 ∨ p3527 ∨ (¬ p4330) ∨ p2459 ∨ (¬ p2951) ∨ (¬ p2249) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h62582 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u12)))))))))))))))))))))

theorem step95865 (p2417 p2651 p3037 p3166 p3172 p3631 p3817 p4044 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h73468 : p3817 ∨ p3631)
    (h45774 : (¬ p2417) ∨ (¬ p2651) ∨ (¬ p3037) ∨ (¬ p3172) ∨ (¬ p3817) ∨ (¬ p4044))
    : (¬ p3037) ∨ (¬ p2417) ∨ p3166 ∨ (¬ p4044) ∨ p3631 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3037 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45774 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step95866 (p2352 p2553 p2588 p3037 p3527 p3548 p3550 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h73282 : p2588 ∨ p2553)
    (h72104 : (¬ p2588) ∨ (¬ p2352) ∨ (¬ p3548) ∨ (¬ p3037) ∨ (¬ p3550))
    : p3527 ∨ (¬ p3550) ∨ (¬ p2352) ∨ (¬ p3037) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h72104 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1)))))))))))

end ElevenRUP
