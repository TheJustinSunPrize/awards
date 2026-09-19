import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step86297 (p2352 p2363 p2774 p2780 p3366 p3367 p3956 p4342 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73308 : p2780 ∨ p2774)
    (h73500 : p3956 ∨ p2352)
    (h45389 : (¬ p2780) ∨ (¬ p3366) ∨ (¬ p3367) ∨ (¬ p3956) ∨ (¬ p4342) ∨ (¬ p4347))
    : (¬ p4342) ∨ p2363 ∨ (¬ p3367) ∨ p2774 ∨ (¬ p3366) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4342 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h45389 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step86298 (p2363 p2774 p2780 p2819 p3366 p3367 p4347 p4358 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73308 : p2780 ∨ p2774)
    (h73564 : p4358 ∨ p2819)
    (h62037 : (¬ p2780) ∨ (¬ p3366) ∨ (¬ p3367) ∨ (¬ p4347) ∨ (¬ p4358))
    : p2363 ∨ (¬ p3366) ∨ p2774 ∨ (¬ p3367) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62037 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step86299 (p2122 p2553 p2696 p2774 p2780 p3822 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73472 : p3822 ∨ p2122)
    (h43978 : (¬ p2553) ∨ (¬ p2696) ∨ (¬ p2780) ∨ (¬ p3822))
    : p2774 ∨ p2122 ∨ (¬ p2696) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43978 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step86302 (p2774 p2780 p2829 p3366 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h34667 : (¬ p2780) ∨ (¬ p2829) ∨ (¬ p3366))
    : p2774 ∨ (¬ p2829) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h34667 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step86304 (p2122 p2553 p2598 p2774 p2780 p3822 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73472 : p3822 ∨ p2122)
    (h54599 : (¬ p2553) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (¬ p3822))
    : p2774 ∨ p2122 ∨ (¬ p2598) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h54599 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step86305 (p2132 p2284 p2774 p2780 p4428 p4906 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h50691 : (¬ p2132) ∨ (¬ p2284) ∨ (¬ p2780) ∨ (¬ p4428) ∨ (¬ p4906))
    : (¬ p2132) ∨ (¬ p4428) ∨ (¬ p4906) ∨ (¬ p2284) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4428 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50691 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86307 (p2177 p2598 p2717 p2774 p2780 p3659 p3689 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h73308 : p2780 ∨ p2774)
    (h45352 : (¬ p2177) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (¬ p3659) ∨ (¬ p3689))
    : p2717 ∨ p2774 ∨ (¬ p2177) ∨ (¬ p3689) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3689 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45352 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step86309 (p2630 p2696 p2774 p2780 p2829 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h44044 : (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2780) ∨ (¬ p2829))
    : p2774 ∨ (¬ p2829) ∨ (¬ p2630) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h44044 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step86312 (p2774 p2780 p2829 p3379 p3873 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h71656 : (¬ p2780) ∨ (¬ p3379) ∨ (¬ p2829) ∨ (¬ p3873))
    : (¬ p2829) ∨ (¬ p3873) ∨ (¬ p3379) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71656 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step86314 (p2132 p2192 p2774 p2780 p4428 p4878 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h53460 : (¬ p2132) ∨ (¬ p2192) ∨ (¬ p2780) ∨ (¬ p4428) ∨ (¬ p4878))
    : p2774 ∨ (¬ p4878) ∨ (¬ p4428) ∨ (¬ p2192) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p4878 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4428 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h53460 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step86318 (p2241 p2750 p2774 p2780 p2829 p3873 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h42276 : (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2780) ∨ (¬ p2829) ∨ (¬ p3873))
    : (¬ p3873) ∨ p2774 ∨ (¬ p2750) ∨ (¬ p2829) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3873 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42276 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step86320 (p2363 p2373 p2406 p2774 p2780 p3379 p3609 p4078 p4340 p4433 p4736 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h73308 : p2780 ∨ p2774)
    (h59317 : (¬ p2363) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p2780) ∨ (¬ p3379) ∨ (¬ p4078) ∨ (¬ p4340) ∨ (¬ p4433) ∨ (¬ p4736))
    : p3609 ∨ (¬ p4078) ∨ (¬ p4433) ∨ p2774 ∨ (¬ p4736) ∨ (¬ p2406) ∨ (¬ p3379) ∨ (¬ p2363) ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p4078 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h59317 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step86322 (p2122 p2177 p2299 p2373 p2406 p2774 p2780 p3379 p3822 p4736 p4902 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73472 : p3822 ∨ p2122)
    (h73234 : p2299 ∨ p2177)
    (h52758 : (¬ p2299) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p2780) ∨ (¬ p3379) ∨ (¬ p3822) ∨ (¬ p4736) ∨ (¬ p4902))
    : p2774 ∨ p2122 ∨ (¬ p3379) ∨ (¬ p4902) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p4736) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h52758 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step86324 (p2598 p2774 p2780 p3016 p4342 p4750 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h51332 : (¬ p2598) ∨ (¬ p2780) ∨ (¬ p3016) ∨ (¬ p4342) ∨ (¬ p4750))
    : p2774 ∨ (¬ p4342) ∨ (¬ p2598) ∨ (¬ p3016) ∨ (¬ p4750) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p4342 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h51332 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step86326 (p2230 p2363 p2774 p2780 p2819 p2982 p3367 p3759 p4347 p4358 p4450 p4734 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73308 : p2780 ∨ p2774)
    (h73564 : p4358 ∨ p2819)
    (h72735 : p4734)
    (h59275 : (¬ p2230) ∨ (¬ p2780) ∨ (¬ p2982) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4450) ∨ (¬ p4734))
    : p2363 ∨ (¬ p4450) ∨ p2774 ∨ p2819 ∨ (¬ p2982) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p4734 := h72735;
    (Or.elim h59275 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (r7 u11)))))))))))))))))))

theorem step86327 (p2774 p2780 p3425 p3471 p3917 p4475 p4620 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73396 : p3471 ∨ p3425)
    (h58659 : (¬ p2780) ∨ (¬ p3471) ∨ (¬ p3917) ∨ (¬ p4475) ∨ (¬ p4620))
    : p2774 ∨ (¬ p3917) ∨ p3425 ∨ (¬ p4620) ∨ (¬ p4475) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h58659 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step86329 (p2363 p2696 p2774 p2780 p2819 p4347 p4358 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73564 : p4358 ∨ p2819)
    (h73308 : p2780 ∨ p2774)
    (h55809 : (¬ p2696) ∨ (¬ p2780) ∨ (¬ p4347) ∨ (¬ p4358))
    : p2363 ∨ p2819 ∨ p2774 ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h55809 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step86331 (p2363 p2598 p2774 p2780 p2819 p4347 p4358 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73564 : p4358 ∨ p2819)
    (h73308 : p2780 ∨ p2774)
    (h59956 : (¬ p2598) ∨ (¬ p2780) ∨ (¬ p4347) ∨ (¬ p4358))
    : p2363 ∨ p2819 ∨ (¬ p2598) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h59956 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step86333 (p2774 p2780 p2829 p2839 p2870 p3583 p3873 p4244 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73308 : p2780 ∨ p2774)
    (h73424 : p3583 ∨ p2839)
    (h47447 : (¬ p2780) ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p3873) ∨ (¬ p4244))
    : (¬ p2829) ∨ p2870 ∨ p2774 ∨ (¬ p3873) ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47447 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step86334 (p2493 p2598 p2774 p2780 p4342 p5217 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h41519 : (¬ p2493) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (¬ p4342) ∨ (¬ p5217))
    : p2774 ∨ (¬ p4342) ∨ (¬ p2598) ∨ (¬ p5217) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p4342 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5217 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41519 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step86336 (p2098 p2553 p2588 p2774 p2780 p3156 p3497 p4188 p4342 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73282 : p2588 ∨ p2553)
    (h73400 : p3497 ∨ p3156)
    (h45363 : (¬ p2098) ∨ (¬ p2588) ∨ (¬ p2780) ∨ (¬ p3497) ∨ (¬ p4188) ∨ (¬ p4342))
    : (¬ p2098) ∨ (¬ p4188) ∨ p2774 ∨ (¬ p4342) ∨ p2553 ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4188 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4342 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u8 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h45363 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step86338 (p2122 p2246 p2396 p2744 p2774 p2780 p2946 p3146 p3156 p3366 p3822 p4107 p4669 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73514 : p4107 ∨ p2396)
    (h73472 : p3822 ∨ p2122)
    (h62987 : (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3366) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4669))
    : p2774 ∨ p2396 ∨ (¬ p3156) ∨ (¬ p4669) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p2246) ∨ (¬ p2946) ∨ p2122 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h62987 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step86341 (p2598 p2774 p2780 p4375 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h37710 : (¬ p2598) ∨ (¬ p2780) ∨ (¬ p4375))
    : p2774 ∨ (¬ p4375) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h37710 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step86342 (p2122 p2598 p2774 p2780 p3367 p3585 p3822 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73472 : p3822 ∨ p2122)
    (h73428 : p3585 ∨ p3367)
    (h62033 : (¬ p2598) ∨ (¬ p2780) ∨ (¬ p3585) ∨ (¬ p3822))
    : p2774 ∨ p2122 ∨ (¬ p2598) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62033 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step86343 (p2598 p2737 p2774 p2780 p3367 p3585 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73428 : p3585 ∨ p3367)
    (h42798 : (¬ p2598) ∨ (¬ p2737) ∨ (¬ p2780) ∨ (¬ p3585))
    : (¬ p2737) ∨ p2774 ∨ (¬ p2598) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42798 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step86344 (p2553 p2588 p2598 p2774 p2780 p3367 p3585 p4342 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73428 : p3585 ∨ p3367)
    (h73282 : p2588 ∨ p2553)
    (h46867 : (¬ p2588) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (¬ p3585) ∨ (¬ p4342))
    : p2774 ∨ (¬ p4342) ∨ (¬ p2598) ∨ p3367 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p4342 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46867 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step86350 (p2122 p2396 p2774 p2780 p2911 p2922 p3379 p3822 p4107 p4666 p4736 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73472 : p3822 ∨ p2122)
    (h73308 : p2780 ∨ p2774)
    (h50867 : (¬ p2780) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4666) ∨ (¬ p4736))
    : (¬ p2911) ∨ p2396 ∨ (¬ p2922) ∨ p2122 ∨ (¬ p4666) ∨ (¬ p3379) ∨ p2774 ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h50867 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step86353 (p2440 p2774 p2780 p2829 p3367 p3585 p4343 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h73308 : p2780 ∨ p2774)
    (h44685 : (¬ p2440) ∨ (¬ p2780) ∨ (¬ p2829) ∨ (¬ p3585) ∨ (¬ p4343))
    : (¬ p2829) ∨ p3367 ∨ (¬ p4343) ∨ (¬ p2440) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3367) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h44685 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86356 (p2563 p2598 p2774 p2780 p3367 p3585 p4428 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73428 : p3585 ∨ p3367)
    (h56620 : (¬ p2563) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (¬ p3585) ∨ (¬ p4428))
    : p2774 ∨ (¬ p4428) ∨ (¬ p2563) ∨ (¬ p2598) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p4428 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56620 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step86357 (p2396 p2417 p2598 p2774 p2780 p3689 p4106 p4278 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73546 : p4278 ∨ p2417)
    (h45066 : (¬ p2396) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (¬ p3689) ∨ (¬ p4106) ∨ (¬ p4278))
    : p2774 ∨ p2417 ∨ (¬ p4106) ∨ (¬ p3689) ∨ (¬ p2598) ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4106 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3689 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45066 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step86359 (p2122 p2230 p2396 p2440 p2774 p2780 p3343 p3822 p4107 p4395 p4419 p4952 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73308 : p2780 ∨ p2774)
    (h73514 : p4107 ∨ p2396)
    (h61431 : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2780) ∨ (¬ p3343) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p4419) ∨ (¬ p4952))
    : (¬ p4952) ∨ (¬ p2230) ∨ p2122 ∨ (¬ p4395) ∨ p2774 ∨ (¬ p4419) ∨ p2396 ∨ (¬ p2440) ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4952 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h61431 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step86360 (p2363 p2449 p2737 p2774 p2780 p2807 p2811 p2819 p3950 p4347 p4358 p4734 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73564 : p4358 ∨ p2819)
    (h72735 : p4734)
    (h73560 : p4347 ∨ p2363)
    (h57731 : (¬ p2449) ∨ (¬ p2737) ∨ (¬ p2780) ∨ (¬ p2807) ∨ (¬ p2811) ∨ (¬ p3950) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4734))
    : (¬ p2811) ∨ p2774 ∨ (¬ p2807) ∨ p2819 ∨ (¬ p2737) ∨ (¬ p3950) ∨ (¬ p2449) ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2811 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4734 := h72735;
    let u11 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h57731 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u10)))))))))))))))))))

theorem step86362 (p2630 p2737 p2743 p2774 p2780 p2810 p2829 p3873 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73316 : p2810 ∨ p2630)
    (h73298 : p2743 ∨ p2737)
    (h46197 : (¬ p2743) ∨ (¬ p2780) ∨ (¬ p2810) ∨ (¬ p2829) ∨ (¬ p3873))
    : (¬ p2829) ∨ p2774 ∨ p2630 ∨ p2737 ∨ (¬ p3873) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46197 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step86364 (p2122 p2177 p2253 p2299 p2774 p2780 p2946 p2992 p3189 p3662 p3822 p4311 p4736 p4902 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73234 : p2299 ∨ p2177)
    (h73472 : p3822 ∨ p2122)
    (h73440 : p3662 ∨ p2992)
    (h55261 : (¬ p2253) ∨ (¬ p2299) ∨ (¬ p2780) ∨ (¬ p2946) ∨ (¬ p3189) ∨ (¬ p3662) ∨ (¬ p3822) ∨ (¬ p4311) ∨ (¬ p4736) ∨ (¬ p4902))
    : (¬ p3189) ∨ p2774 ∨ (¬ p2946) ∨ (¬ p4736) ∨ p2177 ∨ p2122 ∨ p2992 ∨ (¬ p4902) ∨ (¬ p2253) ∨ (¬ p4311) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h55261 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step86366 (p2696 p2774 p2780 p3323 p3461 p4037 p4191 p4337 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73508 : p4037 ∨ p3323)
    (h73308 : p2780 ∨ p2774)
    (h46522 : (¬ p2696) ∨ (¬ p2780) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4337))
    : p3461 ∨ (¬ p4337) ∨ p3323 ∨ p2774 ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p4337 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46522 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step86367 (p2210 p2241 p2247 p2363 p2744 p2774 p2780 p2819 p2972 p3366 p4347 p4358 p4450 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73564 : p4358 ∨ p2819)
    (h73308 : p2780 ∨ p2774)
    (h73226 : p2247 ∨ p2241)
    (h63965 : (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p2972) ∨ (¬ p3366) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4450))
    : (¬ p2972) ∨ p2363 ∨ p2819 ∨ (¬ p2744) ∨ p2774 ∨ (¬ p3366) ∨ (¬ p4450) ∨ p2241 ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h63965 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step86368 (p2246 p2744 p2774 p2780 p2946 p3156 p3366 p3461 p3917 p3969 p4191 p5119 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73308 : p2780 ∨ p2774)
    (h52512 : (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3366) ∨ (¬ p3917) ∨ (¬ p3969) ∨ (¬ p4191) ∨ (¬ p5119))
    : (¬ p3969) ∨ p3461 ∨ (¬ p3917) ∨ (¬ p5119) ∨ (¬ p2744) ∨ p2774 ∨ (¬ p3366) ∨ (¬ p2246) ∨ (¬ p2946) ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h52512 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step86370 (p2363 p2417 p2774 p2780 p2819 p2922 p3379 p3950 p4347 p4358 p4736 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73564 : p4358 ∨ p2819)
    (h73308 : p2780 ∨ p2774)
    (h50257 : (¬ p2417) ∨ (¬ p2780) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3950) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4736))
    : p2363 ∨ (¬ p4736) ∨ (¬ p3379) ∨ (¬ p2922) ∨ p2819 ∨ p2774 ∨ (¬ p3950) ∨ (¬ p2417) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h50257 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step86375 (p2122 p2177 p2230 p2299 p2373 p2774 p2780 p3367 p3759 p3822 p4734 p4902 : Prop)
    (h72735 : p4734)
    (h73308 : p2780 ∨ p2774)
    (h73472 : p3822 ∨ p2122)
    (h73234 : p2299 ∨ p2177)
    (h59290 : (¬ p2230) ∨ (¬ p2299) ∨ (¬ p2373) ∨ (¬ p2780) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p3822) ∨ (¬ p4734) ∨ (¬ p4902))
    : (¬ p3759) ∨ (¬ p3367) ∨ (¬ p2230) ∨ p2774 ∨ p2122 ∨ p2177 ∨ (¬ p4902) ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3759 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4734 := h72735;
    let u9 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h59290 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step86377 (p2230 p2774 p2780 p2850 p3362 p3684 p5221 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73308 : p2780 ∨ p2774)
    (h41095 : (¬ p2230) ∨ (¬ p2780) ∨ (¬ p3362) ∨ (¬ p3684) ∨ (¬ p5221))
    : p2850 ∨ (¬ p2230) ∨ (¬ p3362) ∨ (¬ p5221) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5221 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41095 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step86378 (p2144 p2774 p2780 p2870 p3051 p4244 p4392 p4842 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73308 : p2780 ∨ p2774)
    (h63276 : (¬ p2144) ∨ (¬ p2780) ∨ (¬ p3051) ∨ (¬ p4244) ∨ (¬ p4392) ∨ (¬ p4842))
    : p2870 ∨ p2774 ∨ (¬ p4842) ∨ (¬ p3051) ∨ (¬ p4392) ∨ (¬ p2144) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h63276 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step86380 (p2132 p2774 p2780 p2829 p3367 p3585 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73428 : p3585 ∨ p3367)
    (h47404 : (¬ p2132) ∨ (¬ p2780) ∨ (¬ p2829) ∨ (¬ p3585))
    : p2774 ∨ (¬ p2829) ∨ (¬ p2132) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47404 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step86382 (p2122 p2230 p2373 p2396 p2774 p2780 p3146 p3822 p4107 p4419 p4669 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73514 : p4107 ∨ p2396)
    (h73472 : p3822 ∨ p2122)
    (h59720 : (¬ p2230) ∨ (¬ p2373) ∨ (¬ p2780) ∨ (¬ p3146) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4419) ∨ (¬ p4669))
    : p2774 ∨ p2396 ∨ (¬ p4669) ∨ (¬ p4419) ∨ (¬ p2373) ∨ p2122 ∨ (¬ p2230) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h59720 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step86383 (p2341 p2417 p2696 p2774 p2780 p2911 p3644 p3759 p3917 p4625 p4749 p5201 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73434 : p3644 ∨ p2911)
    (h64359 : (¬ p2341) ∨ (¬ p2417) ∨ (¬ p2696) ∨ (¬ p2780) ∨ (¬ p3644) ∨ (¬ p3759) ∨ (¬ p3917) ∨ (¬ p4625) ∨ (¬ p4749) ∨ (¬ p5201))
    : p2774 ∨ (¬ p3917) ∨ (¬ p4749) ∨ (¬ p5201) ∨ (¬ p2696) ∨ (¬ p3759) ∨ (¬ p2341) ∨ (¬ p2417) ∨ p2911 ∨ (¬ p4625) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h64359 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step86387 (p2098 p2774 p2780 p2829 p3367 p3585 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73428 : p3585 ∨ p3367)
    (h46423 : (¬ p2098) ∨ (¬ p2780) ∨ (¬ p2829) ∨ (¬ p3585))
    : (¬ p2098) ∨ p2774 ∨ (¬ p2829) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46423 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step86388 (p2630 p2651 p2774 p2780 p2810 p4117 p4842 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73316 : p2810 ∨ p2630)
    (h40957 : (¬ p2651) ∨ (¬ p2780) ∨ (¬ p2810) ∨ (¬ p4117) ∨ (¬ p4842))
    : (¬ p2651) ∨ p2774 ∨ (¬ p4117) ∨ p2630 ∨ (¬ p4842) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h40957 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step86390 (p2122 p2177 p2299 p2696 p2774 p2780 p3822 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73472 : p3822 ∨ p2122)
    (h73234 : p2299 ∨ p2177)
    (h58445 : (¬ p2299) ∨ (¬ p2696) ∨ (¬ p2780) ∨ (¬ p3822))
    : p2774 ∨ p2122 ∨ (¬ p2696) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h58445 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step86391 (p2122 p2696 p2737 p2743 p2774 p2780 p3822 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73472 : p3822 ∨ p2122)
    (h73298 : p2743 ∨ p2737)
    (h43454 : (¬ p2696) ∨ (¬ p2743) ∨ (¬ p2780) ∨ (¬ p3822))
    : p2774 ∨ p2122 ∨ (¬ p2696) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43454 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step86392 (p2696 p2774 p2780 p4426 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h20856 : (¬ p2696) ∨ (¬ p2780) ∨ (¬ p4426))
    : p2774 ∨ (¬ p4426) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h20856 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step86396 (p2274 p2774 p2780 p3097 p3425 p3471 p4401 p4475 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73396 : p3471 ∨ p3425)
    (h73352 : p3097 ∨ p2274)
    (h42327 : (¬ p2780) ∨ (¬ p3097) ∨ (¬ p3471) ∨ (¬ p4401) ∨ (¬ p4475))
    : (¬ p4475) ∨ p2774 ∨ p3425 ∨ p2274 ∨ (¬ p4401) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4475 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4401 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42327 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step86399 (p2774 p2780 p3309 p3425 p3471 p3549 p4475 p4867 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73396 : p3471 ∨ p3425)
    (h73406 : p3549 ∨ p3309)
    (h43130 : (¬ p2780) ∨ (¬ p3471) ∨ (¬ p3549) ∨ (¬ p4475) ∨ (¬ p4867))
    : p2774 ∨ (¬ p4475) ∨ (¬ p4867) ∨ p3425 ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p4475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4867 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43130 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86400 (p2553 p2588 p2774 p2780 p3425 p3471 p4475 p5225 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73282 : p2588 ∨ p2553)
    (h73396 : p3471 ∨ p3425)
    (h49713 : (¬ p2588) ∨ (¬ p2780) ∨ (¬ p3471) ∨ (¬ p4475) ∨ (¬ p5225))
    : (¬ p4475) ∨ p2774 ∨ p2553 ∨ (¬ p5225) ∨ p3425 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4475 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5225 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49713 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step86401 (p2774 p2780 p3425 p3471 p3689 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73396 : p3471 ∨ p3425)
    (h20062 : (¬ p2780) ∨ (¬ p3471) ∨ (¬ p3689))
    : p2774 ∨ (¬ p3689) ∨ p3425 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p3689 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20062 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u1)))))))

theorem step86404 (p2737 p2774 p2780 p3425 p3471 p4400 p4424 p4842 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73396 : p3471 ∨ p3425)
    (h41965 : (¬ p2737) ∨ (¬ p2780) ∨ (¬ p3471) ∨ (¬ p4400) ∨ (¬ p4424) ∨ (¬ p4842))
    : (¬ p4424) ∨ p2774 ∨ p3425 ∨ (¬ p4400) ∨ (¬ p2737) ∨ (¬ p4842) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4424 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4400 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41965 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step86406 (p2132 p2774 p2780 p3105 p4428 p5046 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h49386 : (¬ p2132) ∨ (¬ p2780) ∨ (¬ p3105) ∨ (¬ p4428) ∨ (¬ p5046))
    : (¬ p3105) ∨ p2774 ∨ (¬ p2132) ∨ (¬ p4428) ∨ (¬ p5046) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4428 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5046 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h49386 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step86408 (p2641 p2696 p2751 p2774 p2780 p4337 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h53979 : (¬ p2641) ∨ (¬ p2696) ∨ (¬ p2751) ∨ (¬ p2780) ∨ (¬ p4337))
    : p2774 ∨ (¬ p2641) ∨ (¬ p4337) ∨ (¬ p2751) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4337 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h53979 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86409 (p2696 p2727 p2742 p2774 p2780 p4337 p4972 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h41282 : (¬ p2696) ∨ (¬ p2727) ∨ (¬ p2742) ∨ (¬ p2780) ∨ (¬ p4337) ∨ (¬ p4972))
    : p2774 ∨ (¬ p2742) ∨ (¬ p2727) ∨ (¬ p2696) ∨ (¬ p4337) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4337 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41282 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step86411 (p2122 p2177 p2299 p2737 p2774 p2780 p3366 p3822 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73234 : p2299 ∨ p2177)
    (h73472 : p3822 ∨ p2122)
    (h47254 : (¬ p2299) ∨ (¬ p2737) ∨ (¬ p2780) ∨ (¬ p3366) ∨ (¬ p3822))
    : p2774 ∨ (¬ p2737) ∨ p2177 ∨ (¬ p3366) ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47254 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step86416 (p2122 p2177 p2230 p2246 p2299 p2440 p2663 p2744 p2774 p2780 p3343 p3366 p3822 p4451 p4668 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73472 : p3822 ∨ p2122)
    (h73234 : p2299 ∨ p2177)
    (h52809 : (¬ p2230) ∨ (¬ p2246) ∨ (¬ p2299) ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p3343) ∨ (¬ p3366) ∨ (¬ p3822) ∨ (¬ p4451) ∨ (¬ p4668))
    : (¬ p2230) ∨ (¬ p3343) ∨ (¬ p2663) ∨ p2774 ∨ (¬ p2744) ∨ (¬ p4668) ∨ (¬ p4451) ∨ (¬ p2246) ∨ p2122 ∨ (¬ p2440) ∨ p2177 ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4451 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u14 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h52809 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u14))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u13))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u6))) (fun r10 => (False.elim (r10 u5)))))))))))))))))))))))))

theorem step86419 (p2246 p2363 p2417 p2437 p2651 p2744 p2774 p2780 p2819 p3366 p3950 p4347 p4358 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73308 : p2780 ∨ p2774)
    (h73564 : p4358 ∨ p2819)
    (h58088 : (¬ p2246) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p3366) ∨ (¬ p3950) ∨ (¬ p4347) ∨ (¬ p4358))
    : p2363 ∨ (¬ p3366) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2417) ∨ (¬ p3950) ∨ (¬ p2437) ∨ p2774 ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u12 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h58088 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u12)))))))))))))))))))))

theorem step86421 (p2098 p2641 p2727 p2774 p2780 p4111 p4337 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73518 : p4111 ∨ p2727)
    (h45012 : (¬ p2098) ∨ (¬ p2641) ∨ (¬ p2780) ∨ (¬ p4111) ∨ (¬ p4337))
    : (¬ p2098) ∨ p2774 ∨ (¬ p4337) ∨ p2727 ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4337 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45012 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86423 (p2132 p2373 p2619 p2774 p2780 p3880 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73308 : p2780 ∨ p2774)
    (h43845 : (¬ p2132) ∨ (¬ p2619) ∨ (¬ p2780) ∨ (¬ p3880))
    : (¬ p2132) ∨ (¬ p2619) ∨ p2373 ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43845 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86424 (p2132 p2774 p2780 p2819 p2839 p3583 p4358 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73424 : p3583 ∨ p2839)
    (h73564 : p4358 ∨ p2819)
    (h43155 : (¬ p2132) ∨ (¬ p2780) ∨ (¬ p3583) ∨ (¬ p4358))
    : p2774 ∨ (¬ p2132) ∨ p2839 ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43155 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step86426 (p2132 p2774 p2780 p2839 p3583 p3917 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73424 : p3583 ∨ p2839)
    (h60233 : (¬ p2132) ∨ (¬ p2780) ∨ (¬ p3583) ∨ (¬ p3917))
    : p2774 ∨ (¬ p2132) ∨ p2839 ∨ (¬ p3917) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h60233 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step86428 (p2098 p2352 p2774 p2780 p3956 p4326 p5225 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73500 : p3956 ∨ p2352)
    (h42535 : (¬ p2098) ∨ (¬ p2780) ∨ (¬ p3956) ∨ (¬ p4326) ∨ (¬ p5225))
    : (¬ p2098) ∨ (¬ p4326) ∨ p2774 ∨ (¬ p5225) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4326 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5225 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42535 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step86430 (p2098 p2187 p2774 p2780 p3989 p4326 p4401 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73502 : p3989 ∨ p2187)
    (h54482 : (¬ p2098) ∨ (¬ p2780) ∨ (¬ p3989) ∨ (¬ p4326) ∨ (¬ p4401))
    : (¬ p2098) ∨ p2774 ∨ p2187 ∨ (¬ p4326) ∨ (¬ p4401) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4326 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4401 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h54482 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step86431 (p2132 p2774 p2780 p2870 p4428 p4558 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h51006 : (¬ p2132) ∨ (¬ p2780) ∨ (¬ p2870) ∨ (¬ p4428) ∨ (¬ p4558))
    : p2774 ∨ (¬ p2132) ∨ (¬ p2870) ∨ (¬ p4428) ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4428 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h51006 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step86433 (p2132 p2737 p2774 p2780 p2839 p3583 p4842 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73424 : p3583 ∨ p2839)
    (h45718 : (¬ p2132) ∨ (¬ p2737) ∨ (¬ p2780) ∨ (¬ p3583) ∨ (¬ p4842))
    : p2774 ∨ (¬ p2737) ∨ (¬ p2132) ∨ p2839 ∨ (¬ p4842) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45718 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step86435 (p2122 p2396 p2440 p2542 p2651 p2774 p2780 p2982 p3822 p4107 p4395 p4786 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73472 : p3822 ∨ p2122)
    (h73514 : p4107 ∨ p2396)
    (h73270 : p2542 ∨ p2440)
    (h53884 : (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2780) ∨ (¬ p2982) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p4786))
    : p2774 ∨ p2122 ∨ (¬ p2651) ∨ p2396 ∨ (¬ p2982) ∨ (¬ p4395) ∨ p2440 ∨ (¬ p4786) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h53884 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step86436 (p2098 p2187 p2774 p2780 p3989 p4401 p4417 p4967 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73502 : p3989 ∨ p2187)
    (h42310 : (¬ p2098) ∨ (¬ p2780) ∨ (¬ p3989) ∨ (¬ p4401) ∨ (¬ p4417) ∨ (¬ p4967))
    : (¬ p2098) ∨ p2774 ∨ (¬ p4417) ∨ p2187 ∨ (¬ p4967) ∨ (¬ p4401) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4967 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4401 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42310 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step86437 (p2122 p2177 p2241 p2247 p2299 p2744 p2774 p2780 p3037 p3366 p3399 p3822 p3931 p5564 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73234 : p2299 ∨ p2177)
    (h73472 : p3822 ∨ p2122)
    (h73308 : p2780 ∨ p2774)
    (h58697 : (¬ p2247) ∨ (¬ p2299) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p3037) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3822) ∨ (¬ p3931) ∨ (¬ p5564))
    : (¬ p3399) ∨ p2241 ∨ (¬ p2744) ∨ (¬ p5564) ∨ p2177 ∨ p2122 ∨ (¬ p3931) ∨ (¬ p3037) ∨ (¬ p3366) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h58697 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u13))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step86440 (p2187 p2598 p2774 p2780 p2819 p4358 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73564 : p4358 ∨ p2819)
    (h45338 : (¬ p2187) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (¬ p4358))
    : p2774 ∨ (¬ p2598) ∨ (¬ p2187) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45338 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step86447 (p2098 p2774 p2780 p2946 p2952 p3146 p3156 p3361 p3497 p3692 p3979 p4326 p4842 p5122 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73308 : p2780 ∨ p2774)
    (h73400 : p3497 ∨ p3156)
    (h73330 : p2952 ∨ p2946)
    (h63146 : (¬ p2098) ∨ (¬ p2780) ∨ (¬ p2952) ∨ (¬ p3361) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p3979) ∨ (¬ p4326) ∨ (¬ p4842) ∨ (¬ p5122))
    : (¬ p2098) ∨ p3146 ∨ (¬ p3979) ∨ (¬ p3361) ∨ (¬ p4326) ∨ p2774 ∨ p3156 ∨ (¬ p4842) ∨ (¬ p5122) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4326 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h63146 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u13))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step86448 (p2295 p2668 p2774 p2780 p2819 p3568 p4358 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73308 : p2780 ∨ p2774)
    (h73564 : p4358 ∨ p2819)
    (h45286 : (¬ p2668) ∨ (¬ p2780) ∨ (¬ p3568) ∨ (¬ p4358))
    : (¬ p2668) ∨ p2295 ∨ p2774 ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45286 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step86450 (p2352 p2553 p2588 p2774 p2780 p2819 p4358 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73308 : p2780 ∨ p2774)
    (h73564 : p4358 ∨ p2819)
    (h46978 : (¬ p2352) ∨ (¬ p2588) ∨ (¬ p2780) ∨ (¬ p4358))
    : (¬ p2352) ∨ p2553 ∨ p2774 ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46978 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step86451 (p2553 p2588 p2774 p2780 p3564 p3917 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73282 : p2588 ∨ p2553)
    (h57188 : (¬ p2588) ∨ (¬ p2780) ∨ (¬ p3564) ∨ (¬ p3917))
    : (¬ p3917) ∨ p2774 ∨ p2553 ∨ (¬ p3564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3917 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h57188 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step86454 (p2274 p2295 p2696 p2774 p2780 p3568 p4337 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73416 : p3568 ∨ p2295)
    (h61947 : (¬ p2274) ∨ (¬ p2696) ∨ (¬ p2780) ∨ (¬ p3568) ∨ (¬ p4337))
    : p2774 ∨ (¬ p4337) ∨ (¬ p2696) ∨ (¬ p2274) ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p4337 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h61947 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step86455 (p2122 p2253 p2274 p2641 p2774 p2780 p3166 p3189 p3822 p4360 p4564 p4736 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73566 : p4360 ∨ p3189)
    (h73472 : p3822 ∨ p2122)
    (h56747 : (¬ p2253) ∨ (¬ p2274) ∨ (¬ p2641) ∨ (¬ p2780) ∨ (¬ p3166) ∨ (¬ p3822) ∨ (¬ p4360) ∨ (¬ p4564) ∨ (¬ p4736))
    : (¬ p2641) ∨ p2774 ∨ (¬ p4736) ∨ (¬ p3166) ∨ p3189 ∨ p2122 ∨ (¬ p4564) ∨ (¬ p2253) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h56747 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step86456 (p2122 p2187 p2274 p2774 p2780 p3822 p3989 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73308 : p2780 ∨ p2774)
    (h73502 : p3989 ∨ p2187)
    (h47299 : (¬ p2274) ∨ (¬ p2780) ∨ (¬ p3822) ∨ (¬ p3989))
    : p2122 ∨ p2774 ∨ p2187 ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47299 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step86458 (p2122 p2132 p2274 p2774 p2780 p3822 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73308 : p2780 ∨ p2774)
    (h48124 : (¬ p2132) ∨ (¬ p2274) ∨ (¬ p2780) ∨ (¬ p3822))
    : p2122 ∨ p2774 ∨ (¬ p2274) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h48124 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86459 (p2122 p2187 p2274 p2774 p2780 p3822 p3873 p3989 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73308 : p2780 ∨ p2774)
    (h73502 : p3989 ∨ p2187)
    (h56114 : (¬ p2274) ∨ (¬ p2780) ∨ (¬ p3822) ∨ (¬ p3873) ∨ (¬ p3989))
    : p2122 ∨ p2774 ∨ (¬ p2274) ∨ (¬ p3873) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56114 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step86461 (p2598 p2774 p2780 p3125 p3917 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h45328 : (¬ p2598) ∨ (¬ p2780) ∨ (¬ p3125) ∨ (¬ p3917))
    : p2774 ∨ (¬ p3917) ∨ (¬ p2598) ∨ (¬ p3125) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45328 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step86464 (p2363 p2774 p2780 p2819 p3266 p4347 p4358 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73560 : p4347 ∨ p2363)
    (h73564 : p4358 ∨ p2819)
    (h73308 : p2780 ∨ p2774)
    (h42944 : (¬ p2780) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4444))
    : p3266 ∨ p2363 ∨ p2819 ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42944 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86469 (p2122 p2177 p2299 p2774 p2780 p3146 p3166 p3256 p3692 p3822 p4786 p4902 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73234 : p2299 ∨ p2177)
    (h73308 : p2780 ∨ p2774)
    (h73472 : p3822 ∨ p2122)
    (h52155 : (¬ p2299) ∨ (¬ p2780) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p3822) ∨ (¬ p4786) ∨ (¬ p4902))
    : (¬ p3166) ∨ p3146 ∨ (¬ p3256) ∨ p2177 ∨ (¬ p4786) ∨ p2774 ∨ p2122 ∨ (¬ p4902) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h52155 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step86473 (p2122 p2774 p2780 p3166 p3256 p3266 p3822 p4260 p4786 p4831 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73472 : p3822 ∨ p2122)
    (h56225 : (¬ p2780) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3822) ∨ (¬ p4260) ∨ (¬ p4786) ∨ (¬ p4831))
    : (¬ p4260) ∨ (¬ p3266) ∨ (¬ p4831) ∨ (¬ p4786) ∨ p2774 ∨ p2122 ∨ (¬ p3166) ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4260 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h56225 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step86474 (p2122 p2295 p2696 p2774 p2780 p3822 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73308 : p2780 ∨ p2774)
    (h49023 : (¬ p2295) ∨ (¬ p2696) ∨ (¬ p2780) ∨ (¬ p3822))
    : p2122 ∨ p2774 ∨ (¬ p2696) ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h49023 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86479 (p2122 p2774 p2780 p3309 p3319 p3822 p3873 p4026 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73472 : p3822 ∨ p2122)
    (h73504 : p4026 ∨ p3319)
    (h47078 : (¬ p2780) ∨ (¬ p3309) ∨ (¬ p3822) ∨ (¬ p3873) ∨ (¬ p4026))
    : (¬ p3309) ∨ p2774 ∨ (¬ p3873) ∨ p2122 ∨ p3319 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47078 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step86482 (p2774 p2780 p2901 p2946 p3461 p3917 p4129 p4191 p4786 p4826 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73308 : p2780 ∨ p2774)
    (h62200 : (¬ p2780) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3917) ∨ (¬ p4129) ∨ (¬ p4191) ∨ (¬ p4786) ∨ (¬ p4826))
    : (¬ p4129) ∨ p3461 ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p4826) ∨ (¬ p3917) ∨ (¬ p4786) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4129 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h62200 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step86486 (p2774 p2777 p2781 : Prop)
    (h73306 : p2777 ∨ p2774)
    (h3684 : (¬ p2777) ∨ p2781)
    : p2774 ∨ p2781 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2781) := (fun h => hn (Or.inr h));
    let u2 : p2777 := (Or.elim h73306 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h3684 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step86487 (p2774 p2777 p2782 : Prop)
    (h73306 : p2777 ∨ p2774)
    (h3685 : (¬ p2777) ∨ p2782)
    : p2774 ∨ p2782 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2782) := (fun h => hn (Or.inr h));
    let u2 : p2777 := (Or.elim h73306 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h3685 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step86489 (p2737 p2748 p2752 : Prop)
    (h73303 : (¬ p2737) ∨ (¬ p2752))
    (h3628 : p2748 ∨ p2752)
    : p2748 ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2748) := (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2752) := (Or.elim h73303 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h3628 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step86491 (p2449 p2651 p2657 p2807 p3246 p3690 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73288 : p2657 ∨ p2651)
    (h46596 : (¬ p2449) ∨ (¬ p2657) ∨ (¬ p2807) ∨ (¬ p3690))
    : p3246 ∨ (¬ p2449) ∨ (¬ p2807) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46596 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86492 (p2264 p2449 p3399 p3553 p3631 p3817 p4366 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73468 : p3817 ∨ p3631)
    (h73410 : p3553 ∨ p2264)
    (h46801 : (¬ p2449) ∨ (¬ p3553) ∨ (¬ p3817) ∨ (¬ p4366))
    : p3399 ∨ p3631 ∨ (¬ p2449) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3631) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46801 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86494 (p2156 p2192 p2417 p2449 p2807 p2891 p2959 p3486 p3646 p4277 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73398 : p3486 ∨ p2891)
    (h73436 : p3646 ∨ p2156)
    (h59083 : (¬ p2192) ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p2959) ∨ (¬ p3486) ∨ (¬ p3646) ∨ (¬ p4277) ∨ (¬ p4278))
    : p2417 ∨ (¬ p2449) ∨ p2891 ∨ (¬ p2192) ∨ p2156 ∨ (¬ p2959) ∨ (¬ p2807) ∨ (¬ p4277) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h59083 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u8)))))))))))))))))

theorem step86496 (p2264 p2449 p2528 p2534 p3553 p4420 p4443 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73410 : p3553 ∨ p2264)
    (h48986 : (¬ p2449) ∨ (¬ p2534) ∨ (¬ p3553) ∨ (¬ p4420) ∨ (¬ p4443))
    : (¬ p2449) ∨ p2528 ∨ (¬ p4443) ∨ (¬ p4420) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4443 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48986 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86502 (p2264 p2449 p2737 p2743 p3361 p3516 p3553 p3821 p4849 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h73470 : p3821 ∨ p3516)
    (h73298 : p2743 ∨ p2737)
    (h48433 : (¬ p2449) ∨ (¬ p2743) ∨ (¬ p3361) ∨ (¬ p3553) ∨ (¬ p3821) ∨ (¬ p4849))
    : (¬ p4849) ∨ (¬ p2449) ∨ p2264 ∨ p3516 ∨ (¬ p3361) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4849 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h48433 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step86503 (p2166 p2449 p2891 p3246 p3486 p3690 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73398 : p3486 ∨ p2891)
    (h43596 : (¬ p2166) ∨ (¬ p2449) ∨ (¬ p3486) ∨ (¬ p3690))
    : p3246 ∨ (¬ p2449) ∨ (¬ p2166) ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43596 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86504 (p2449 p2995 p3051 p3156 p3246 p3497 p3556 p3690 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73400 : p3497 ∨ p3156)
    (h73414 : p3556 ∨ p3051)
    (h58998 : (¬ p2449) ∨ (¬ p2995) ∨ (¬ p3497) ∨ (¬ p3556) ∨ (¬ p3690))
    : p3246 ∨ (¬ p2449) ∨ (¬ p2995) ∨ p3156 ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h58998 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step86505 (p2264 p2449 p2707 p2717 p3553 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h58365 : (¬ p2449) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p3553))
    : (¬ p2717) ∨ (¬ p2707) ∨ p2264 ∨ (¬ p2449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h58365 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86506 (p2252 p2449 p2685 p2745 p3516 p3821 p4849 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h59713 : (¬ p2252) ∨ (¬ p2449) ∨ (¬ p2685) ∨ (¬ p2745) ∨ (¬ p3821) ∨ (¬ p4849))
    : (¬ p4849) ∨ (¬ p2449) ∨ (¬ p2252) ∨ p3516 ∨ (¬ p2745) ∨ (¬ p2685) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4849 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h59713 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step86510 (p2396 p2449 p2553 p2588 p4107 p4156 p4976 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73282 : p2588 ∨ p2553)
    (h48723 : (¬ p2449) ∨ (¬ p2588) ∨ (¬ p4107) ∨ (¬ p4156) ∨ (¬ p4976))
    : (¬ p2449) ∨ p2396 ∨ (¬ p4976) ∨ (¬ p4156) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4976 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48723 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86511 (p2449 p2946 p3516 p3580 p3821 p4704 p4849 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73046 : p4704)
    (h57269 : (¬ p2449) ∨ (¬ p2946) ∨ (¬ p3580) ∨ (¬ p3821) ∨ (¬ p4704) ∨ (¬ p4849))
    : p3516 ∨ (¬ p2449) ∨ (¬ p2946) ∨ (¬ p3580) ∨ (¬ p4849) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4849 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4704 := h73046;
    (Or.elim h57269 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step86519 (p2449 p2870 p2995 p3516 p3821 p4244 p4283 p4906 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73540 : p4244 ∨ p2870)
    (h64492 : (¬ p2449) ∨ (¬ p2995) ∨ (¬ p3821) ∨ (¬ p4244) ∨ (¬ p4283) ∨ (¬ p4906))
    : p3516 ∨ (¬ p2449) ∨ p2870 ∨ (¬ p2995) ∨ (¬ p4906) ∨ (¬ p4283) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h64492 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step86520 (p2341 p2396 p2449 p2881 p3551 p4107 p4155 p4559 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73514 : p4107 ∨ p2396)
    (h54110 : (¬ p2449) ∨ (¬ p2881) ∨ (¬ p3551) ∨ (¬ p4107) ∨ (¬ p4155) ∨ (¬ p4559))
    : p2341 ∨ p2396 ∨ (¬ p4559) ∨ (¬ p2881) ∨ (¬ p4155) ∨ (¬ p2449) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h54110 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step86521 (p2307 p2313 p2396 p2449 p2807 p4107 p4583 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73238 : p2313 ∨ p2307)
    (h61517 : (¬ p2313) ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p4107) ∨ (¬ p4583))
    : (¬ p2449) ∨ p2396 ∨ (¬ p4583) ∨ p2307 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61517 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86522 (p2298 p2396 p2449 p4107 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h20213 : (¬ p2298) ∨ (¬ p2449) ∨ (¬ p4107))
    : (¬ p2449) ∨ (¬ p2298) ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2298 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20213 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u3)))))))

theorem step86523 (p2177 p2396 p2449 p2807 p4107 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h45741 : (¬ p2177) ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p4107))
    : (¬ p2449) ∨ p2396 ∨ (¬ p2807) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45741 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86525 (p2264 p2417 p2449 p2881 p3553 p4277 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73410 : p3553 ∨ p2264)
    (h61503 : (¬ p2449) ∨ (¬ p2881) ∨ (¬ p3553) ∨ (¬ p4277) ∨ (¬ p4278))
    : (¬ p2449) ∨ p2417 ∨ (¬ p2881) ∨ p2264 ∨ (¬ p4277) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61503 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step86526 (p2449 p2807 p2881 p3246 p3690 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h47430 : (¬ p2449) ∨ (¬ p2807) ∨ (¬ p2881) ∨ (¬ p3690))
    : p3246 ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h47430 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86530 (p2417 p2449 p2807 p2911 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h51922 : (¬ p2449) ∨ (¬ p2807) ∨ (¬ p2911) ∨ (¬ p4278))
    : p2417 ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h51922 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86531 (p2122 p2396 p2449 p3822 p4107 p4156 p4843 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73472 : p3822 ∨ p2122)
    (h49626 : (¬ p2449) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4156) ∨ (¬ p4843))
    : (¬ p2449) ∨ p2396 ∨ p2122 ∨ (¬ p4156) ∨ (¬ p4843) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4843 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h49626 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step86532 (p2284 p2417 p2449 p2995 p3569 p3952 p4278 p4558 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73496 : p3952 ∨ p2284)
    (h60402 : (¬ p2449) ∨ (¬ p2995) ∨ (¬ p3569) ∨ (¬ p3952) ∨ (¬ p4278) ∨ (¬ p4558))
    : p2417 ∨ (¬ p2449) ∨ (¬ p3569) ∨ (¬ p2995) ∨ (¬ p4558) ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h60402 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step86536 (p2264 p2341 p2449 p2598 p3055 p3422 p3553 p3564 p3584 p4137 p4625 p5257 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h73350 : p3055 ∨ p2598)
    (h73426 : p3584 ∨ p3422)
    (h73410 : p3553 ∨ p2264)
    (h42344 : (¬ p2341) ∨ (¬ p2449) ∨ (¬ p3055) ∨ (¬ p3553) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4625) ∨ (¬ p5257))
    : (¬ p2341) ∨ (¬ p2449) ∨ p3564 ∨ p2598 ∨ p3422 ∨ p2264 ∨ (¬ p4625) ∨ (¬ p5257) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h42344 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step86537 (p2449 p2761 p2807 p3266 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h47291 : (¬ p2449) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p4444))
    : p3266 ∨ (¬ p2761) ∨ (¬ p2449) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h47291 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86539 (p2241 p2352 p2383 p2387 p2449 p2996 p3027 p3564 p4137 p4625 p5021 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h73340 : p3027 ∨ p2996)
    (h73246 : p2387 ∨ p2383)
    (h54905 : (¬ p2241) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p4137) ∨ (¬ p4625) ∨ (¬ p5021))
    : p3564 ∨ (¬ p2352) ∨ (¬ p5021) ∨ (¬ p4625) ∨ p2996 ∨ (¬ p2449) ∨ p2383 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h54905 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step86541 (p2132 p2187 p2264 p2449 p2860 p3516 p3553 p3821 p4133 p5260 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73410 : p3553 ∨ p2264)
    (h65142 : (¬ p2132) ∨ (¬ p2187) ∨ (¬ p2449) ∨ (¬ p2860) ∨ (¬ p3553) ∨ (¬ p3821) ∨ (¬ p4133) ∨ (¬ p5260))
    : (¬ p2449) ∨ (¬ p2860) ∨ (¬ p2187) ∨ p3516 ∨ (¬ p2132) ∨ (¬ p5260) ∨ (¬ p4133) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h65142 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step86542 (p2417 p2440 p2449 p3580 p4278 p4646 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h40919 : (¬ p2440) ∨ (¬ p2449) ∨ (¬ p3580) ∨ (¬ p4278) ∨ (¬ p4646))
    : p2417 ∨ (¬ p2449) ∨ (¬ p2440) ∨ (¬ p4646) ∨ (¬ p3580) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h40919 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step86545 (p2427 p2449 p2995 p3246 p3690 p4235 p4705 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73536 : p4235 ∨ p2427)
    (h48959 : (¬ p2449) ∨ (¬ p2995) ∨ (¬ p3690) ∨ (¬ p4235) ∨ (¬ p4705))
    : p3246 ∨ (¬ p2449) ∨ (¬ p2995) ∨ (¬ p4705) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48959 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step86547 (p2417 p2441 p2449 p3083 p3580 p4256 p4278 p4608 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73542 : p4256 ∨ p3083)
    (h41912 : (¬ p2441) ∨ (¬ p2449) ∨ (¬ p3580) ∨ (¬ p4256) ∨ (¬ p4278) ∨ (¬ p4608))
    : p2417 ∨ (¬ p2449) ∨ p3083 ∨ (¬ p2441) ∨ (¬ p4608) ∨ (¬ p3580) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41912 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step86548 (p2417 p2441 p2449 p3016 p3574 p3580 p4278 p4715 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73422 : p3574 ∨ p3016)
    (h50329 : (¬ p2441) ∨ (¬ p2449) ∨ (¬ p3574) ∨ (¬ p3580) ∨ (¬ p4278) ∨ (¬ p4715))
    : p2417 ∨ (¬ p2449) ∨ (¬ p2441) ∨ p3016 ∨ (¬ p3580) ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50329 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step86549 (p2417 p2441 p2449 p2870 p3699 p4278 p4885 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h60407 : (¬ p2441) ∨ (¬ p2449) ∨ (¬ p2870) ∨ (¬ p3699) ∨ (¬ p4278) ∨ (¬ p4885))
    : p2417 ∨ (¬ p2449) ∨ (¬ p2441) ∨ (¬ p3699) ∨ (¬ p4885) ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3699 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h60407 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step86551 (p2449 p3246 p3690 p3699 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h5400 : (¬ p2449) ∨ (¬ p3690) ∨ (¬ p3699))
    : (¬ p2449) ∨ (¬ p3699) ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3699 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h5400 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step86552 (p2417 p2441 p2449 p3051 p3699 p4278 p4539 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h55802 : (¬ p2441) ∨ (¬ p2449) ∨ (¬ p3051) ∨ (¬ p3699) ∨ (¬ p4278) ∨ (¬ p4539))
    : p2417 ∨ (¬ p2449) ∨ (¬ p3699) ∨ (¬ p4539) ∨ (¬ p3051) ∨ (¬ p2441) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3699 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4539 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h55802 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step86553 (p2449 p2807 p3166 p3172 p4548 p4668 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h48059 : (¬ p2449) ∨ (¬ p2807) ∨ (¬ p3172) ∨ (¬ p4548) ∨ (¬ p4668))
    : p3166 ∨ (¬ p2449) ∨ (¬ p4548) ∨ (¬ p4668) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48059 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step86562 (p2870 p4893 p4895 : Prop)
    (h73814 : p4893 ∨ p2870)
    (h8070 : (¬ p4893) ∨ p4895)
    : p2870 ∨ p4895 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4895) := (fun h => hn (Or.inr h));
    let u2 : p4893 := (Or.elim h73814 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h8070 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step86563 (p2870 p4244 p4898 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h44721 : (¬ p4244) ∨ p4898)
    : p2870 ∨ p4898 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4898) := (fun h => hn (Or.inr h));
    let u2 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h44721 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step86564 (p2870 p4244 p4885 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h45437 : (¬ p4244) ∨ p4885)
    : p2870 ∨ p4885 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4885) := (fun h => hn (Or.inr h));
    let u2 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45437 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step86565 (p2132 p2138 p2192 p2870 p2891 p4173 p4244 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73214 : p2138 ∨ p2132)
    (h73528 : p4173 ∨ p2192)
    (h52420 : (¬ p2138) ∨ (¬ p2891) ∨ (¬ p4173) ∨ (¬ p4244))
    : p2870 ∨ p2132 ∨ p2192 ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52420 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86569 (p2459 p2839 p2870 p2881 p3570 p3583 p4244 p4348 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73562 : p4348 ∨ p2459)
    (h73540 : p4244 ∨ p2870)
    (h73424 : p3583 ∨ p2839)
    (h43142 : (¬ p3570) ∨ (¬ p3583) ∨ (¬ p4244) ∨ (¬ p4348))
    : p2881 ∨ p2459 ∨ p2870 ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43142 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step86570 (p2210 p2870 p3399 p3555 p3571 p4244 p4878 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73540 : p4244 ∨ p2870)
    (h49960 : (¬ p3399) ∨ (¬ p3555) ∨ (¬ p3571) ∨ (¬ p4244) ∨ (¬ p4878))
    : (¬ p3399) ∨ p2210 ∨ (¬ p4878) ∨ p2870 ∨ (¬ p3571) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4878 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3571 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49960 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86573 (p2210 p2870 p2891 p3105 p4244 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h54070 : (¬ p2210) ∨ (¬ p2891) ∨ (¬ p3105) ∨ (¬ p4244))
    : (¬ p3105) ∨ p2870 ∨ (¬ p2210) ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h54070 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86577 (p2210 p2619 p2870 p2891 p4244 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h44549 : (¬ p2210) ∨ (¬ p2619) ∨ (¬ p2891) ∨ (¬ p4244))
    : (¬ p2619) ∨ p2870 ∨ (¬ p2891) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h44549 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86578 (p2210 p2860 p2870 p2891 p4244 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h45219 : (¬ p2210) ∨ (¬ p2860) ∨ (¬ p2891) ∨ (¬ p4244))
    : p2870 ∨ (¬ p2210) ∨ (¬ p2860) ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45219 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86579 (p2737 p2839 p2870 p2881 p3570 p3583 p4244 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73418 : p3570 ∨ p2881)
    (h73424 : p3583 ∨ p2839)
    (h63272 : (¬ p2737) ∨ (¬ p3570) ∨ (¬ p3583) ∨ (¬ p4244))
    : (¬ p2737) ∨ p2870 ∨ p2881 ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63272 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86580 (p2608 p2839 p2870 p2881 p3570 p3583 p3954 p4244 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73498 : p3954 ∨ p2608)
    (h73540 : p4244 ∨ p2870)
    (h73418 : p3570 ∨ p2881)
    (h47358 : (¬ p3570) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p4244))
    : p2839 ∨ p2608 ∨ p2870 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2839) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47358 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step86584 (p2248 p2264 p2608 p2807 p2839 p2870 p2911 p3583 p3644 p3954 p4244 p4277 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73424 : p3583 ∨ p2839)
    (h73498 : p3954 ∨ p2608)
    (h73540 : p4244 ∨ p2870)
    (h58186 : (¬ p2248) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p3583) ∨ (¬ p3644) ∨ (¬ p3954) ∨ (¬ p4244) ∨ (¬ p4277))
    : p2911 ∨ (¬ p2264) ∨ p2839 ∨ p2608 ∨ (¬ p2807) ∨ (¬ p2248) ∨ p2870 ∨ (¬ p4277) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h58186 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step86586 (p2563 p2608 p2839 p2870 p3583 p3872 p3954 p4244 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73424 : p3583 ∨ p2839)
    (h73540 : p4244 ∨ p2870)
    (h45736 : (¬ p2563) ∨ (¬ p3583) ∨ (¬ p3872) ∨ (¬ p3954) ∨ (¬ p4244))
    : (¬ p3872) ∨ p2608 ∨ (¬ p2563) ∨ p2839 ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3872 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45736 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step86587 (p2608 p2839 p2870 p3246 p3583 p3690 p3954 p4244 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73446 : p3690 ∨ p3246)
    (h73424 : p3583 ∨ p2839)
    (h73540 : p4244 ∨ p2870)
    (h59390 : (¬ p3583) ∨ (¬ p3690) ∨ (¬ p3954) ∨ (¬ p4244))
    : p2608 ∨ p3246 ∨ p2839 ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h59390 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u7)))))))))

theorem step86588 (p2248 p2396 p2449 p2608 p2807 p2839 p2870 p3583 p3954 p4107 p4244 p4559 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73514 : p4107 ∨ p2396)
    (h73498 : p3954 ∨ p2608)
    (h73424 : p3583 ∨ p2839)
    (h48857 : (¬ p2248) ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p4107) ∨ (¬ p4244) ∨ (¬ p4559))
    : (¬ p2449) ∨ p2870 ∨ (¬ p4559) ∨ (¬ p2807) ∨ p2396 ∨ (¬ p2248) ∨ p2608 ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h48857 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step86593 (p2696 p2737 p2839 p2870 p3365 p3583 p3873 p4244 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73540 : p4244 ∨ p2870)
    (h73390 : p3365 ∨ p2696)
    (h46360 : (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3583) ∨ (¬ p3873) ∨ (¬ p4244))
    : (¬ p2737) ∨ p2839 ∨ p2870 ∨ (¬ p3873) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46360 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step86594 (p2132 p2138 p2870 p3051 p3873 p4244 p4521 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73214 : p2138 ∨ p2132)
    (h52525 : (¬ p2138) ∨ (¬ p3051) ∨ (¬ p3873) ∨ (¬ p4244) ∨ (¬ p4521))
    : p2870 ∨ p2132 ∨ (¬ p3873) ∨ (¬ p4521) ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h52525 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step86597 (p2132 p2138 p2241 p2264 p2870 p2996 p3027 p3246 p3690 p4244 p4666 p4736 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73214 : p2138 ∨ p2132)
    (h73340 : p3027 ∨ p2996)
    (h73540 : p4244 ∨ p2870)
    (h49551 : (¬ p2138) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p3027) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4666) ∨ (¬ p4736))
    : p3246 ∨ (¬ p2264) ∨ (¬ p4736) ∨ (¬ p4666) ∨ (¬ p2241) ∨ p2132 ∨ p2996 ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h49551 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step86598 (p2132 p2138 p2696 p2737 p2743 p2870 p4244 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73298 : p2743 ∨ p2737)
    (h73540 : p4244 ∨ p2870)
    (h42934 : (¬ p2138) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p4244))
    : p2132 ∨ p2737 ∨ p2870 ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42934 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step86599 (p2144 p2839 p2870 p3051 p3583 p4244 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73424 : p3583 ∨ p2839)
    (h71659 : (¬ p3583) ∨ (¬ p4244) ∨ (¬ p2144) ∨ (¬ p3051))
    : p2870 ∨ p2839 ∨ (¬ p2144) ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71659 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step86601 (p2132 p2138 p2363 p2870 p3063 p3093 p3246 p3690 p4244 p4669 p4736 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73540 : p4244 ∨ p2870)
    (h73214 : p2138 ∨ p2132)
    (h51905 : (¬ p2138) ∨ (¬ p2363) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4669) ∨ (¬ p4736))
    : (¬ p3063) ∨ p3246 ∨ p2870 ∨ (¬ p4736) ∨ (¬ p3093) ∨ p2132 ∨ (¬ p4669) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h51905 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step86602 (p2341 p2619 p2870 p3551 p4042 p4244 p4986 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73408 : p3551 ∨ p2341)
    (h42463 : (¬ p2619) ∨ (¬ p3551) ∨ (¬ p4042) ∨ (¬ p4244) ∨ (¬ p4986))
    : (¬ p2619) ∨ p2870 ∨ p2341 ∨ (¬ p4986) ∨ (¬ p4042) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42463 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step86603 (p2132 p2138 p2177 p2870 p3093 p3246 p3309 p3690 p4244 p4666 p4736 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73214 : p2138 ∨ p2132)
    (h73540 : p4244 ∨ p2870)
    (h59750 : (¬ p2138) ∨ (¬ p2177) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4666) ∨ (¬ p4736))
    : (¬ p3309) ∨ p3246 ∨ (¬ p2177) ∨ (¬ p4666) ∨ (¬ p3093) ∨ p2132 ∨ (¬ p4736) ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h59750 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step86605 (p2132 p2138 p2352 p2363 p2573 p2870 p3246 p3690 p4244 p4419 p4669 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73446 : p3690 ∨ p3246)
    (h73214 : p2138 ∨ p2132)
    (h57767 : (¬ p2138) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4419) ∨ (¬ p4669))
    : (¬ p2352) ∨ p2870 ∨ (¬ p4669) ∨ p3246 ∨ (¬ p2573) ∨ (¬ p4419) ∨ (¬ p2363) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h57767 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step86607 (p2252 p2331 p2860 p2870 p2963 p2992 p3745 p4244 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73540 : p4244 ∨ p2870)
    (h56440 : (¬ p2252) ∨ (¬ p2860) ∨ (¬ p2963) ∨ (¬ p2992) ∨ (¬ p3745) ∨ (¬ p4244))
    : (¬ p2992) ∨ (¬ p3745) ∨ p2331 ∨ (¬ p2860) ∨ (¬ p2252) ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h56440 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step86608 (p2187 p2860 p2870 p4244 p4275 p4405 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h50255 : (¬ p2187) ∨ (¬ p2860) ∨ (¬ p4244) ∨ (¬ p4275) ∨ (¬ p4405))
    : p2870 ∨ (¬ p2187) ∨ (¬ p4405) ∨ (¬ p2860) ∨ (¬ p4275) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h50255 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86611 (p2860 p2870 p3758 p3872 p4244 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73455 : (¬ p2860) ∨ (¬ p3758))
    (h6551 : p3758 ∨ (¬ p3872) ∨ (¬ p4244))
    : p2870 ∨ (¬ p3872) ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p3758) := (Or.elim h73455 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h6551 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step86617 (p2406 p2563 p2860 p2870 p3238 p4110 p4244 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73374 : p3238 ∨ p2406)
    (h73516 : p4110 ∨ p2563)
    (h45451 : (¬ p2860) ∨ (¬ p3238) ∨ (¬ p4110) ∨ (¬ p4244))
    : (¬ p2860) ∨ p2870 ∨ p2406 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2860 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45451 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86619 (p2132 p2138 p2241 p2727 p2870 p2881 p3083 p3570 p4244 p4420 p4736 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73540 : p4244 ∨ p2870)
    (h73418 : p3570 ∨ p2881)
    (h51259 : (¬ p2138) ∨ (¬ p2241) ∨ (¬ p2727) ∨ (¬ p3083) ∨ (¬ p3570) ∨ (¬ p4244) ∨ (¬ p4420) ∨ (¬ p4736))
    : p2132 ∨ p2870 ∨ (¬ p4736) ∨ (¬ p4420) ∨ (¬ p2727) ∨ p2881 ∨ (¬ p2241) ∨ (¬ p3083) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h51259 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step86620 (p2870 p3246 p3516 p3690 p4244 p4988 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73540 : p4244 ∨ p2870)
    (h71661 : (¬ p3516) ∨ (¬ p3690) ∨ (¬ p4988) ∨ (¬ p4244))
    : (¬ p3516) ∨ p3246 ∨ p2870 ∨ (¬ p4988) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h71661 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step86621 (p2132 p2138 p2528 p2651 p2870 p3083 p3246 p3690 p4244 p4669 p4786 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73214 : p2138 ∨ p2132)
    (h73540 : p4244 ∨ p2870)
    (h52165 : (¬ p2138) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4669) ∨ (¬ p4786))
    : p3246 ∨ p2132 ∨ p2870 ∨ (¬ p4669) ∨ (¬ p2528) ∨ (¬ p3083) ∨ (¬ p2651) ∨ (¬ p4786) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52165 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step86624 (p2132 p2138 p2427 p2598 p2870 p4244 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73540 : p4244 ∨ p2870)
    (h44241 : (¬ p2138) ∨ (¬ p2427) ∨ (¬ p2598) ∨ (¬ p4244))
    : p2132 ∨ p2870 ∨ (¬ p2598) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h44241 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step86625 (p2132 p2138 p2870 p2881 p3570 p4244 p5558 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73418 : p3570 ∨ p2881)
    (h73540 : p4244 ∨ p2870)
    (h44809 : (¬ p2138) ∨ (¬ p3570) ∨ (¬ p4244) ∨ (¬ p5558))
    : (¬ p5558) ∨ p2132 ∨ p2881 ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5558 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44809 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step86626 (p2132 p2138 p2737 p2870 p2881 p3366 p3570 p4244 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73540 : p4244 ∨ p2870)
    (h73418 : p3570 ∨ p2881)
    (h63304 : (¬ p2138) ∨ (¬ p2737) ∨ (¬ p3366) ∨ (¬ p3570) ∨ (¬ p4244))
    : p2132 ∨ (¬ p2737) ∨ (¬ p3366) ∨ p2870 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63304 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step86629 (p2132 p2138 p2696 p2870 p2901 p4244 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73540 : p4244 ∨ p2870)
    (h45263 : (¬ p2138) ∨ (¬ p2696) ∨ (¬ p2901) ∨ (¬ p4244))
    : (¬ p2901) ∨ p2132 ∨ p2870 ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45263 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step86630 (p2619 p2870 p2901 p3146 p4244 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h60660 : (¬ p2619) ∨ (¬ p2901) ∨ (¬ p3146) ∨ (¬ p4244))
    : (¬ p2901) ∨ (¬ p2619) ∨ (¬ p3146) ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60660 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86631 (p2295 p2860 p2870 p4244 p4275 p4560 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h72955 : p4560)
    (h41639 : (¬ p2295) ∨ (¬ p2860) ∨ (¬ p4244) ∨ (¬ p4275) ∨ (¬ p4560))
    : p2870 ∨ (¬ p2295) ∨ (¬ p4275) ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4560 := h72955;
    (Or.elim h41639 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step86635 (p2860 p2870 p3737 p4244 p5717 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h45129 : (¬ p2860) ∨ (¬ p3737) ∨ (¬ p4244) ∨ (¬ p5717))
    : (¬ p3737) ∨ (¬ p5717) ∨ (¬ p2860) ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45129 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step86636 (p2136 p2220 p2553 p2619 p2651 p2870 p3016 p4120 p4244 p4559 p4786 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h73540 : p4244 ∨ p2870)
    (h49689 : (¬ p2136) ∨ (¬ p2553) ∨ (¬ p2619) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p4120) ∨ (¬ p4244) ∨ (¬ p4559) ∨ (¬ p4786))
    : (¬ p2553) ∨ p2220 ∨ (¬ p2651) ∨ (¬ p2136) ∨ (¬ p4559) ∨ p2870 ∨ (¬ p2619) ∨ (¬ p4786) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h49689 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step86637 (p2177 p2299 p2619 p2870 p4244 p4275 p4902 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73234 : p2299 ∨ p2177)
    (h63351 : (¬ p2299) ∨ (¬ p2619) ∨ (¬ p4244) ∨ (¬ p4275) ∨ (¬ p4902))
    : (¬ p2619) ∨ p2870 ∨ (¬ p4902) ∨ (¬ p4275) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63351 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86639 (p2341 p2870 p3527 p3551 p4244 p4283 p4431 p4878 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73540 : p4244 ∨ p2870)
    (h50748 : (¬ p3527) ∨ (¬ p3551) ∨ (¬ p4244) ∨ (¬ p4283) ∨ (¬ p4431) ∨ (¬ p4878))
    : (¬ p3527) ∨ (¬ p4878) ∨ (¬ p4431) ∨ (¬ p4283) ∨ p2341 ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4878 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u7 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h50748 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step86642 (p2137 p2156 p2187 p2870 p4244 p4275 p4405 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h48816 : (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p4244) ∨ (¬ p4275) ∨ (¬ p4405))
    : p2870 ∨ (¬ p2156) ∨ (¬ p4275) ∨ (¬ p2137) ∨ (¬ p2187) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48816 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step86646 (p2166 p2191 p2210 p2619 p2870 p3555 p4244 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73540 : p4244 ∨ p2870)
    (h73222 : p2191 ∨ p2166)
    (h45603 : (¬ p2191) ∨ (¬ p2619) ∨ (¬ p3555) ∨ (¬ p4244))
    : (¬ p2619) ∨ p2210 ∨ p2870 ∨ p2166 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2166) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2191 := (Or.elim h73222 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45603 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step86649 (p2144 p2241 p2619 p2750 p2753 p2870 p3051 p3093 p3591 p3923 p4244 p4433 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73432 : p3591 ∨ p3093)
    (h64863 : (¬ p2144) ∨ (¬ p2241) ∨ (¬ p2619) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3051) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4244) ∨ (¬ p4433))
    : p2870 ∨ (¬ p2619) ∨ p3093 ∨ (¬ p2753) ∨ (¬ p2750) ∨ (¬ p3923) ∨ (¬ p4433) ∨ (¬ p2241) ∨ (¬ p3051) ∨ (¬ p2144) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h64863 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step86651 (p2166 p2191 p2563 p2619 p2870 p4210 p4244 p4555 : Prop)
    (h73222 : p2191 ∨ p2166)
    (h73540 : p4244 ∨ p2870)
    (h53383 : (¬ p2191) ∨ (¬ p2563) ∨ (¬ p2619) ∨ (¬ p4210) ∨ (¬ p4244) ∨ (¬ p4555))
    : (¬ p4210) ∨ p2166 ∨ (¬ p2619) ∨ (¬ p4555) ∨ p2870 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2191 := (Or.elim h73222 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h53383 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step86652 (p2352 p2493 p2499 p2619 p2870 p3051 p3379 p3452 p3956 p4244 p4433 p4521 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73500 : p3956 ∨ p2352)
    (h73540 : p4244 ∨ p2870)
    (h73394 : p3452 ∨ p3379)
    (h55412 : (¬ p2499) ∨ (¬ p2619) ∨ (¬ p3051) ∨ (¬ p3452) ∨ (¬ p3956) ∨ (¬ p4244) ∨ (¬ p4433) ∨ (¬ p4521))
    : p2493 ∨ (¬ p3051) ∨ p2352 ∨ (¬ p2619) ∨ p2870 ∨ (¬ p4521) ∨ p3379 ∨ (¬ p4433) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2493) := (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h55412 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step86654 (p2449 p2870 p2995 p3246 p3690 p4244 p4906 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73540 : p4244 ∨ p2870)
    (h62247 : (¬ p2449) ∨ (¬ p2995) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4906))
    : p3246 ∨ (¬ p2449) ∨ (¬ p4906) ∨ (¬ p2995) ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62247 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86655 (p2619 p2870 p3246 p3690 p4042 p4244 p4666 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73446 : p3690 ∨ p3246)
    (h41247 : (¬ p2619) ∨ (¬ p3690) ∨ (¬ p4042) ∨ (¬ p4244) ∨ (¬ p4666))
    : (¬ p2619) ∨ p2870 ∨ (¬ p4666) ∨ p3246 ∨ (¬ p4042) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41247 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86661 (p2373 p2619 p2870 p3051 p3880 p4244 p4539 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73490 : p3880 ∨ p2373)
    (h51533 : (¬ p2619) ∨ (¬ p3051) ∨ (¬ p3880) ∨ (¬ p4244) ∨ (¬ p4539))
    : p2870 ∨ (¬ p2619) ∨ p2373 ∨ (¬ p3051) ∨ (¬ p4539) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4539 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h51533 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step86662 (p2373 p2619 p2870 p2881 p3570 p3880 p4244 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73490 : p3880 ∨ p2373)
    (h73418 : p3570 ∨ p2881)
    (h45421 : (¬ p2619) ∨ (¬ p3570) ∨ (¬ p3880) ∨ (¬ p4244))
    : (¬ p2619) ∨ p2870 ∨ p2373 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45421 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86664 (p2132 p2138 p2241 p2870 p3189 p3246 p3256 p3690 p4244 p4669 p4736 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73214 : p2138 ∨ p2132)
    (h73446 : p3690 ∨ p3246)
    (h49443 : (¬ p2138) ∨ (¬ p2241) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4669) ∨ (¬ p4736))
    : (¬ p3189) ∨ p2870 ∨ (¬ p4669) ∨ p2132 ∨ (¬ p2241) ∨ (¬ p4736) ∨ p3246 ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h49443 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step86668 (p2132 p2138 p2573 p2870 p2881 p3016 p3083 p3570 p3574 p4244 p4419 p4420 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73422 : p3574 ∨ p3016)
    (h73418 : p3570 ∨ p2881)
    (h73214 : p2138 ∨ p2132)
    (h60515 : (¬ p2138) ∨ (¬ p2573) ∨ (¬ p3083) ∨ (¬ p3570) ∨ (¬ p3574) ∨ (¬ p4244) ∨ (¬ p4419) ∨ (¬ p4420))
    : p2870 ∨ p3016 ∨ (¬ p4419) ∨ p2881 ∨ (¬ p2573) ∨ (¬ p4420) ∨ (¬ p3083) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h60515 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step86669 (p2132 p2138 p2363 p2510 p2528 p2573 p2870 p2881 p3570 p4079 p4133 p4244 p4347 p4736 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73418 : p3570 ∨ p2881)
    (h73540 : p4244 ∨ p2870)
    (h73214 : p2138 ∨ p2132)
    (h50323 : (¬ p2138) ∨ (¬ p2510) ∨ (¬ p2528) ∨ (¬ p2573) ∨ (¬ p3570) ∨ (¬ p4079) ∨ (¬ p4133) ∨ (¬ p4244) ∨ (¬ p4347) ∨ (¬ p4736))
    : p2363 ∨ (¬ p2528) ∨ (¬ p4079) ∨ (¬ p2510) ∨ (¬ p4736) ∨ p2881 ∨ (¬ p4133) ∨ (¬ p2573) ∨ p2870 ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2510 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u13 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h50323 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step86671 (p2132 p2138 p2493 p2870 p3246 p3379 p3564 p3690 p4244 p4621 p4736 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73446 : p3690 ∨ p3246)
    (h73540 : p4244 ∨ p2870)
    (h50269 : (¬ p2138) ∨ (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3564) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4621) ∨ (¬ p4736))
    : (¬ p3564) ∨ p2132 ∨ (¬ p3379) ∨ (¬ p2493) ∨ p3246 ∨ (¬ p4621) ∨ p2870 ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h50269 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step86672 (p2132 p2138 p2383 p2781 p2870 p3246 p3266 p3276 p3690 p3990 p4022 p4244 p4444 p4669 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73540 : p4244 ∨ p2870)
    (h73214 : p2138 ∨ p2132)
    (h73446 : p3690 ∨ p3246)
    (h59788 : (¬ p2138) ∨ (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3276) ∨ (¬ p3690) ∨ (¬ p3990) ∨ (¬ p4022) ∨ (¬ p4244) ∨ (¬ p4444) ∨ (¬ p4669))
    : p3266 ∨ p2870 ∨ (¬ p4669) ∨ (¬ p4022) ∨ (¬ p2383) ∨ (¬ p3990) ∨ (¬ p3276) ∨ (¬ p2781) ∨ p2132 ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4022 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u13 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h59788 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u13))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step86674 (p2132 p2138 p2518 p2528 p2870 p3246 p3379 p3690 p4244 p4669 p4736 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73446 : p3690 ∨ p3246)
    (h73540 : p4244 ∨ p2870)
    (h49442 : (¬ p2138) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3379) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4669) ∨ (¬ p4736))
    : (¬ p2518) ∨ (¬ p2528) ∨ p2132 ∨ (¬ p4736) ∨ p3246 ∨ p2870 ∨ (¬ p4669) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h49442 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step86675 (p2619 p2870 p2911 p3644 p4244 p4277 p4312 p4378 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73434 : p3644 ∨ p2911)
    (h41872 : (¬ p2619) ∨ (¬ p3644) ∨ (¬ p4244) ∨ (¬ p4277) ∨ (¬ p4312) ∨ (¬ p4378))
    : (¬ p4378) ∨ (¬ p4312) ∨ (¬ p2619) ∨ p2870 ∨ (¬ p4277) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4378 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41872 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step86676 (p2156 p2860 p2870 p2911 p2934 p3379 p3527 p3644 p3646 p4244 p4277 p4524 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73436 : p3646 ∨ p2156)
    (h72962 : p4524)
    (h73540 : p4244 ∨ p2870)
    (h61532 : (¬ p2860) ∨ (¬ p2934) ∨ (¬ p3379) ∨ (¬ p3527) ∨ (¬ p3644) ∨ (¬ p3646) ∨ (¬ p4244) ∨ (¬ p4277) ∨ (¬ p4524))
    : (¬ p3379) ∨ (¬ p2934) ∨ p2911 ∨ (¬ p4277) ∨ p2156 ∨ p2870 ∨ (¬ p3527) ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3379 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2934 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4524 := h72962;
    let u11 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h61532 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u10)))))))))))))))))))

theorem step86680 (p2156 p2177 p2299 p2860 p2870 p3646 p4244 p4275 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73436 : p3646 ∨ p2156)
    (h73234 : p2299 ∨ p2177)
    (h44924 : (¬ p2299) ∨ (¬ p2860) ∨ (¬ p3646) ∨ (¬ p4244) ∨ (¬ p4275))
    : (¬ p2860) ∨ p2870 ∨ p2156 ∨ p2177 ∨ (¬ p4275) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2860 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44924 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step86684 (p2870 p2957 p2992 p3105 p3662 p4032 p4244 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73540 : p4244 ∨ p2870)
    (h43043 : (¬ p2957) ∨ (¬ p3105) ∨ (¬ p3662) ∨ (¬ p4032) ∨ (¬ p4244))
    : (¬ p3105) ∨ (¬ p4032) ∨ (¬ p2957) ∨ p2992 ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43043 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step86685 (p2406 p2870 p2922 p3238 p3569 p4244 p4882 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73374 : p3238 ∨ p2406)
    (h49304 : (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3569) ∨ (¬ p4244) ∨ (¬ p4882))
    : (¬ p2922) ∨ p2870 ∨ (¬ p4882) ∨ p2406 ∨ (¬ p3569) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4882 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49304 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86686 (p2136 p2220 p2241 p2247 p2619 p2744 p2870 p2922 p3366 p3379 p4120 p4244 p4277 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73522 : p4120 ∨ p2220)
    (h73540 : p4244 ∨ p2870)
    (h53728 : (¬ p2136) ∨ (¬ p2247) ∨ (¬ p2619) ∨ (¬ p2744) ∨ (¬ p2922) ∨ (¬ p3366) ∨ (¬ p3379) ∨ (¬ p4120) ∨ (¬ p4244) ∨ (¬ p4277))
    : p2241 ∨ (¬ p3366) ∨ (¬ p4277) ∨ (¬ p2619) ∨ (¬ p2744) ∨ (¬ p2922) ∨ p2220 ∨ p2870 ∨ (¬ p3379) ∨ (¬ p2136) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h53728 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step86687 (p2177 p2299 p2619 p2870 p4042 p4244 p4559 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h73540 : p4244 ∨ p2870)
    (h48827 : (¬ p2299) ∨ (¬ p2619) ∨ (¬ p4042) ∨ (¬ p4244) ∨ (¬ p4559))
    : (¬ p4042) ∨ (¬ p2619) ∨ p2177 ∨ p2870 ∨ (¬ p4559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4042 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48827 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step86692 (p2870 p2881 p3105 p3570 p4135 p4244 p4668 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73418 : p3570 ∨ p2881)
    (h54904 : (¬ p3105) ∨ (¬ p3570) ∨ (¬ p4135) ∨ (¬ p4244) ∨ (¬ p4668))
    : (¬ p4135) ∨ (¬ p3105) ∨ (¬ p4668) ∨ p2870 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4135 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54904 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86694 (p2132 p2138 p2417 p2870 p2881 p2922 p3379 p3570 p4244 p4668 p4736 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73540 : p4244 ∨ p2870)
    (h73418 : p3570 ∨ p2881)
    (h50322 : (¬ p2138) ∨ (¬ p2417) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3570) ∨ (¬ p4244) ∨ (¬ p4668) ∨ (¬ p4736))
    : (¬ p2417) ∨ p2132 ∨ (¬ p3379) ∨ (¬ p4668) ∨ (¬ p2922) ∨ p2870 ∨ p2881 ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h50322 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step86701 (p2132 p2138 p2241 p2247 p2744 p2870 p3073 p3246 p3366 p3449 p3690 p4244 p4669 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73540 : p4244 ∨ p2870)
    (h73446 : p3690 ∨ p3246)
    (h73214 : p2138 ∨ p2132)
    (h52798 : (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3073) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4669))
    : (¬ p3449) ∨ p2241 ∨ (¬ p4669) ∨ p2870 ∨ (¬ p3073) ∨ p3246 ∨ (¬ p2744) ∨ (¬ p3366) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h52798 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step86704 (p2132 p2138 p2253 p2331 p2641 p2870 p2881 p3189 p3570 p4154 p4244 p4550 p4736 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73214 : p2138 ∨ p2132)
    (h73418 : p3570 ∨ p2881)
    (h73540 : p4244 ∨ p2870)
    (h55550 : (¬ p2138) ∨ (¬ p2253) ∨ (¬ p2331) ∨ (¬ p3189) ∨ (¬ p3570) ∨ (¬ p4154) ∨ (¬ p4244) ∨ (¬ p4550) ∨ (¬ p4736))
    : p2641 ∨ (¬ p3189) ∨ (¬ p4550) ∨ (¬ p4736) ∨ p2132 ∨ p2881 ∨ (¬ p2253) ∨ p2870 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h55550 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step86706 (p2132 p2138 p2573 p2870 p3246 p3367 p3564 p3690 p3759 p4244 p4621 p4734 : Prop)
    (h72735 : p4734)
    (h73214 : p2138 ∨ p2132)
    (h73540 : p4244 ∨ p2870)
    (h73446 : p3690 ∨ p3246)
    (h56660 : (¬ p2138) ∨ (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3564) ∨ (¬ p3690) ∨ (¬ p3759) ∨ (¬ p4244) ∨ (¬ p4621) ∨ (¬ p4734))
    : (¬ p3564) ∨ (¬ p3759) ∨ (¬ p4621) ∨ p2132 ∨ p2870 ∨ (¬ p3367) ∨ (¬ p2573) ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4734 := h72735;
    let u9 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h56660 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step86707 (p2132 p2138 p2573 p2870 p3016 p3246 p3343 p3574 p3690 p4244 p4419 p4638 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73446 : p3690 ∨ p3246)
    (h73214 : p2138 ∨ p2132)
    (h73422 : p3574 ∨ p3016)
    (h51252 : (¬ p2138) ∨ (¬ p2573) ∨ (¬ p3343) ∨ (¬ p3574) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4419) ∨ (¬ p4638))
    : (¬ p3343) ∨ (¬ p4638) ∨ p2870 ∨ p3246 ∨ p2132 ∨ (¬ p4419) ∨ p3016 ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4638 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h51252 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step86708 (p2136 p2156 p2341 p2860 p2870 p2911 p3366 p3379 p3452 p3545 p3644 p3646 p4244 p4277 p4376 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73434 : p3644 ∨ p2911)
    (h73394 : p3452 ∨ p3379)
    (h73436 : p3646 ∨ p2156)
    (h57152 : (¬ p2136) ∨ (¬ p2341) ∨ (¬ p2860) ∨ (¬ p3366) ∨ (¬ p3452) ∨ (¬ p3545) ∨ (¬ p3644) ∨ (¬ p3646) ∨ (¬ p4244) ∨ (¬ p4277) ∨ (¬ p4376))
    : (¬ p2341) ∨ p2870 ∨ (¬ p4277) ∨ p2911 ∨ (¬ p3366) ∨ (¬ p3545) ∨ (¬ p2136) ∨ (¬ p2860) ∨ p3379 ∨ p2156 ∨ (¬ p4376) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3545 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u14 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h57152 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u13))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u14))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (False.elim (r9 u10)))))))))))))))))))))))

theorem step86709 (p2132 p2138 p2383 p2528 p2781 p2870 p3266 p4244 p4432 p4831 p5660 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73214 : p2138 ∨ p2132)
    (h59743 : (¬ p2138) ∨ (¬ p2383) ∨ (¬ p2528) ∨ (¬ p2781) ∨ (¬ p3266) ∨ (¬ p4244) ∨ (¬ p4432) ∨ (¬ p4831) ∨ (¬ p5660))
    : (¬ p2528) ∨ p2870 ∨ (¬ p2781) ∨ (¬ p4831) ∨ (¬ p3266) ∨ (¬ p2383) ∨ p2132 ∨ (¬ p5660) ∨ (¬ p4432) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h59743 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step86710 (p2132 p2138 p2241 p2449 p2870 p2881 p2996 p3027 p3570 p4244 p4668 p4736 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73340 : p3027 ∨ p2996)
    (h73418 : p3570 ∨ p2881)
    (h73540 : p4244 ∨ p2870)
    (h50879 : (¬ p2138) ∨ (¬ p2241) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3570) ∨ (¬ p4244) ∨ (¬ p4668) ∨ (¬ p4736))
    : (¬ p2449) ∨ p2132 ∨ (¬ p2241) ∨ (¬ p4668) ∨ p2996 ∨ p2881 ∨ (¬ p4736) ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h50879 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step86711 (p2132 p2138 p2246 p2744 p2870 p3166 p3256 p3266 p3366 p4244 p4831 p5660 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73540 : p4244 ∨ p2870)
    (h52903 : (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3366) ∨ (¬ p4244) ∨ (¬ p4831) ∨ (¬ p5660))
    : (¬ p5660) ∨ p2132 ∨ (¬ p2744) ∨ (¬ p3266) ∨ (¬ p2246) ∨ (¬ p3166) ∨ (¬ p4831) ∨ (¬ p3366) ∨ (¬ p3256) ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5660 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h52903 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step86713 (p2132 p2138 p2246 p2331 p2744 p2870 p3323 p3366 p3461 p4244 p4831 p5660 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73214 : p2138 ∨ p2132)
    (h52782 : (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2744) ∨ (¬ p3323) ∨ (¬ p3366) ∨ (¬ p3461) ∨ (¬ p4244) ∨ (¬ p4831) ∨ (¬ p5660))
    : (¬ p5660) ∨ (¬ p2246) ∨ (¬ p2331) ∨ p2870 ∨ (¬ p3323) ∨ (¬ p2744) ∨ (¬ p3366) ∨ p2132 ∨ (¬ p3461) ∨ (¬ p4831) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5660 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h52782 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step86715 (p2132 p2138 p2246 p2331 p2363 p2668 p2744 p2870 p3246 p3366 p3690 p4244 p4669 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73214 : p2138 ∨ p2132)
    (h73446 : p3690 ∨ p3246)
    (h61660 : (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4669))
    : (¬ p2668) ∨ (¬ p2246) ∨ (¬ p2363) ∨ (¬ p3366) ∨ p2870 ∨ (¬ p4669) ∨ (¬ p2331) ∨ p2132 ∨ p3246 ∨ (¬ p2744) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h61660 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step86716 (p2427 p2440 p2542 p2870 p4244 p4750 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73270 : p2542 ∨ p2440)
    (h66808 : (¬ p4244) ∨ (¬ p4750) ∨ (¬ p2542) ∨ (¬ p2427))
    : p2870 ∨ p2440 ∨ (¬ p4750) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66808 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step86718 (p2427 p2870 p3695 p4244 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h20862 : (¬ p2427) ∨ (¬ p3695) ∨ (¬ p4244))
    : (¬ p3695) ∨ p2870 ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3695 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h20862 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u3)))))))

theorem step86724 (p2870 p2901 p3115 p4208 p4244 p4322 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h73540 : p4244 ∨ p2870)
    (h54822 : (¬ p2901) ∨ (¬ p4208) ∨ (¬ p4244) ∨ (¬ p4322))
    : (¬ p4322) ∨ p3115 ∨ (¬ p2901) ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54822 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step86725 (p2137 p2156 p2553 p2870 p4244 p4275 p4718 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h41631 : (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2553) ∨ (¬ p4244) ∨ (¬ p4275) ∨ (¬ p4718))
    : (¬ p2137) ∨ (¬ p2553) ∨ (¬ p4275) ∨ (¬ p4718) ∨ p2870 ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2137 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41631 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step86726 (p2563 p2870 p2982 p3105 p4244 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h73540 : p4244 ∨ p2870)
    (h45210 : (¬ p2563) ∨ (¬ p3105) ∨ (¬ p4244) ∨ (¬ p4948))
    : p2982 ∨ p2870 ∨ (¬ p3105) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45210 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86727 (p2156 p2860 p2870 p2957 p2992 p3646 p3662 p4244 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73436 : p3646 ∨ p2156)
    (h73540 : p4244 ∨ p2870)
    (h63926 : (¬ p2860) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3662) ∨ (¬ p4244))
    : (¬ p2860) ∨ p2992 ∨ p2156 ∨ (¬ p2957) ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2860 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63926 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step86734 (p2132 p2138 p2331 p2668 p2737 p2811 p2870 p2881 p3570 p4133 p4244 p4734 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h72735 : p4734)
    (h73540 : p4244 ∨ p2870)
    (h73418 : p3570 ∨ p2881)
    (h51487 : (¬ p2138) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3570) ∨ (¬ p4133) ∨ (¬ p4244) ∨ (¬ p4734))
    : (¬ p2668) ∨ (¬ p2737) ∨ p2132 ∨ p2870 ∨ (¬ p2331) ∨ p2881 ∨ (¬ p4133) ∨ (¬ p2811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p4734 := h72735;
    let u10 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h51487 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step86735 (p2132 p2138 p2241 p2641 p2668 p2870 p2881 p3570 p4133 p4244 p4736 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73540 : p4244 ∨ p2870)
    (h73418 : p3570 ∨ p2881)
    (h50877 : (¬ p2138) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3570) ∨ (¬ p4133) ∨ (¬ p4244) ∨ (¬ p4736))
    : (¬ p2668) ∨ (¬ p2641) ∨ p2132 ∨ (¬ p4133) ∨ p2870 ∨ (¬ p2241) ∨ (¬ p4736) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h50877 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step86737 (p2187 p2819 p2870 p3985 p3989 p4244 p4555 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73502 : p3989 ∨ p2187)
    (h54209 : (¬ p2819) ∨ (¬ p3985) ∨ (¬ p3989) ∨ (¬ p4244) ∨ (¬ p4555))
    : (¬ p2819) ∨ p2870 ∨ (¬ p4555) ∨ p2187 ∨ (¬ p3985) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3985 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54209 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86738 (p2156 p2253 p2651 p2727 p2860 p2870 p2996 p3027 p3646 p4111 p4244 p4280 p4524 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73436 : p3646 ∨ p2156)
    (h73340 : p3027 ∨ p2996)
    (h73540 : p4244 ∨ p2870)
    (h72962 : p4524)
    (h51710 : (¬ p2253) ∨ (¬ p2651) ∨ (¬ p2860) ∨ (¬ p3027) ∨ (¬ p3646) ∨ (¬ p4111) ∨ (¬ p4244) ∨ (¬ p4280) ∨ (¬ p4524))
    : (¬ p2253) ∨ p2727 ∨ p2156 ∨ (¬ p2860) ∨ p2996 ∨ (¬ p2651) ∨ p2870 ∨ (¬ p4280) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2253 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4280 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p4524 := h72962;
    (Or.elim h51710 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u12)))))))))))))))))))

theorem step86742 (p2751 p2870 p2951 p2992 p3051 p4244 p4392 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h41630 : (¬ p2751) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3051) ∨ (¬ p4244) ∨ (¬ p4392))
    : p2870 ∨ (¬ p2951) ∨ (¬ p4392) ∨ (¬ p2992) ∨ (¬ p2751) ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41630 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step86743 (p2839 p2870 p2881 p3367 p3570 p3583 p4244 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73418 : p3570 ∨ p2881)
    (h73540 : p4244 ∨ p2870)
    (h45329 : (¬ p3367) ∨ (¬ p3570) ∨ (¬ p3583) ∨ (¬ p4244))
    : p2839 ∨ (¬ p3367) ∨ p2881 ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2839) := (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45329 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step86747 (p2493 p2509 p2573 p2579 p2619 p2870 p3051 p4108 p4244 p4434 p4521 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73274 : p2579 ∨ p2573)
    (h62572 : (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2579) ∨ (¬ p2619) ∨ (¬ p3051) ∨ (¬ p4108) ∨ (¬ p4244) ∨ (¬ p4434) ∨ (¬ p4521))
    : p2870 ∨ (¬ p2619) ∨ (¬ p2509) ∨ (¬ p3051) ∨ (¬ p2493) ∨ p2573 ∨ (¬ p4521) ∨ (¬ p4434) ∨ (¬ p4108) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h62572 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step86748 (p2144 p2252 p2363 p2619 p2750 p2753 p2870 p3051 p3166 p3172 p3256 p4118 p4244 p4433 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73520 : p4118 ∨ p3256)
    (h73356 : p3172 ∨ p3166)
    (h55338 : (¬ p2144) ∨ (¬ p2252) ∨ (¬ p2363) ∨ (¬ p2619) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3051) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4244) ∨ (¬ p4433))
    : p2870 ∨ p3256 ∨ (¬ p3051) ∨ (¬ p2252) ∨ (¬ p2144) ∨ p3166 ∨ (¬ p2750) ∨ (¬ p2363) ∨ (¬ p2753) ∨ (¬ p2619) ∨ (¬ p4433) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u13 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h55338 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u13))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u11))) (fun r9 => (False.elim (r9 u10)))))))))))))))))))))))

theorem step86751 (p2144 p2363 p2619 p2870 p3051 p3073 p3093 p3591 p4244 p4261 p4371 p4433 p4733 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73544 : p4261 ∨ p3073)
    (h73432 : p3591 ∨ p3093)
    (h50052 : (¬ p2144) ∨ (¬ p2363) ∨ (¬ p2619) ∨ (¬ p3051) ∨ (¬ p3591) ∨ (¬ p4244) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p4433) ∨ (¬ p4733))
    : (¬ p2619) ∨ p2870 ∨ (¬ p4433) ∨ (¬ p3051) ∨ (¬ p2363) ∨ (¬ p4371) ∨ (¬ p4733) ∨ p3073 ∨ p3093 ∨ (¬ p2144) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h50052 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step86753 (p2132 p2138 p2246 p2470 p2663 p2744 p2870 p3083 p3246 p3343 p3366 p3690 p4244 p4256 p4638 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73214 : p2138 ∨ p2132)
    (h73446 : p3690 ∨ p3246)
    (h73542 : p4256 ∨ p3083)
    (h52902 : (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2470) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3343) ∨ (¬ p3366) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4256) ∨ (¬ p4638))
    : (¬ p2470) ∨ (¬ p3343) ∨ (¬ p3366) ∨ (¬ p2246) ∨ (¬ p2663) ∨ p2870 ∨ p2132 ∨ (¬ p2744) ∨ (¬ p4638) ∨ p3246 ∨ p3083 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4638 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u14 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h52902 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u13))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u14))) (fun r9 => (False.elim (r9 u8)))))))))))))))))))))))

theorem step86754 (p2319 p2341 p2870 p2881 p2962 p3570 p4244 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73418 : p3570 ∨ p2881)
    (h71663 : (¬ p2341) ∨ (¬ p3570) ∨ (¬ p2319) ∨ (¬ p4244) ∨ (¬ p2962))
    : (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2962) ∨ p2870 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h71663 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86755 (p2341 p2870 p2881 p3570 p4244 p4988 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73418 : p3570 ∨ p2881)
    (h71664 : (¬ p3570) ∨ (¬ p2341) ∨ (¬ p4244) ∨ (¬ p4988))
    : (¬ p2341) ∨ p2870 ∨ p2881 ∨ (¬ p4988) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h71664 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step86756 (p2132 p2138 p2493 p2499 p2518 p2573 p2870 p2881 p3570 p4079 p4133 p4157 p4244 p4736 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73214 : p2138 ∨ p2132)
    (h73540 : p4244 ∨ p2870)
    (h73260 : p2499 ∨ p2493)
    (h50317 : (¬ p2138) ∨ (¬ p2499) ∨ (¬ p2518) ∨ (¬ p2573) ∨ (¬ p3570) ∨ (¬ p4079) ∨ (¬ p4133) ∨ (¬ p4157) ∨ (¬ p4244) ∨ (¬ p4736))
    : (¬ p4157) ∨ (¬ p2518) ∨ p2881 ∨ (¬ p4133) ∨ (¬ p4736) ∨ (¬ p2573) ∨ p2132 ∨ p2870 ∨ (¬ p4079) ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4157 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u13 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h50317 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step86758 (p2252 p2528 p2534 p2651 p2657 p2750 p2870 p3051 p3083 p3105 p3370 p3371 p4244 p4256 p4450 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73542 : p4256 ∨ p3083)
    (h73288 : p2657 ∨ p2651)
    (h73540 : p4244 ∨ p2870)
    (h42580 : (¬ p2252) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3051) ∨ (¬ p3105) ∨ (¬ p3370) ∨ (¬ p3371) ∨ (¬ p4244) ∨ (¬ p4256) ∨ (¬ p4450))
    : p2528 ∨ (¬ p3370) ∨ (¬ p3105) ∨ (¬ p4450) ∨ p3083 ∨ (¬ p3051) ∨ (¬ p2252) ∨ (¬ p3371) ∨ (¬ p2750) ∨ p2651 ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u13 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u14 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h42580 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u13))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u14))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (False.elim (r9 u3)))))))))))))))))))))))

theorem step86763 (p2144 p2252 p2331 p2363 p2668 p2750 p2753 p2870 p2963 p3051 p3105 p3324 p4244 p4347 p4450 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73560 : p4347 ∨ p2363)
    (h73386 : p3324 ∨ p2668)
    (h73338 : p2963 ∨ p2331)
    (h64552 : (¬ p2144) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2963) ∨ (¬ p3051) ∨ (¬ p3105) ∨ (¬ p3324) ∨ (¬ p4244) ∨ (¬ p4347) ∨ (¬ p4450))
    : p2870 ∨ p2363 ∨ (¬ p3105) ∨ (¬ p4450) ∨ p2668 ∨ (¬ p2753) ∨ (¬ p2144) ∨ p2331 ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u13 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u14 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64552 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u14))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u13))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (False.elim (r9 u3)))))))))))))))))))))))

theorem step86764 (p2144 p2619 p2870 p3051 p3969 p4244 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h47829 : (¬ p2144) ∨ (¬ p2619) ∨ (¬ p3051) ∨ (¬ p3969) ∨ (¬ p4244))
    : (¬ p3969) ∨ p2870 ∨ (¬ p2144) ∨ (¬ p2619) ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47829 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step86765 (p2144 p2696 p2870 p3051 p3365 p4244 p5052 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73390 : p3365 ∨ p2696)
    (h50303 : (¬ p2144) ∨ (¬ p3051) ∨ (¬ p3365) ∨ (¬ p4244) ∨ (¬ p5052))
    : p2870 ∨ (¬ p5052) ∨ (¬ p3051) ∨ p2696 ∨ (¬ p2144) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p5052 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50303 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step86771 (p2132 p2138 p2177 p2870 p2881 p3570 p4244 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73214 : p2138 ∨ p2132)
    (h73540 : p4244 ∨ p2870)
    (h43404 : (¬ p2138) ∨ (¬ p2177) ∨ (¬ p3570) ∨ (¬ p4244))
    : p2881 ∨ p2132 ∨ (¬ p2177) ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43404 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step86772 (p2132 p2138 p2870 p2911 p2922 p3246 p3379 p3690 p4244 p4666 p4736 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73214 : p2138 ∨ p2132)
    (h73540 : p4244 ∨ p2870)
    (h58960 : (¬ p2138) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4666) ∨ (¬ p4736))
    : p3246 ∨ p2132 ∨ (¬ p2911) ∨ (¬ p3379) ∨ p2870 ∨ (¬ p2922) ∨ (¬ p4666) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h58960 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step86775 (p2132 p2138 p2870 p2911 p3246 p3367 p3389 p3690 p3759 p4244 p4666 p4734 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73446 : p3690 ∨ p3246)
    (h73540 : p4244 ∨ p2870)
    (h72735 : p4734)
    (h50666 : (¬ p2138) ∨ (¬ p2911) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3690) ∨ (¬ p3759) ∨ (¬ p4244) ∨ (¬ p4666) ∨ (¬ p4734))
    : p2132 ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p4666) ∨ (¬ p3759) ∨ p3246 ∨ p2870 ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p4734 := h72735;
    (Or.elim h50666 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u11)))))))))))))))))))

theorem step86780 (p2761 p2870 p3105 p3461 p4244 p4381 p5045 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73540 : p4244 ∨ p2870)
    (h51121 : (¬ p3105) ∨ (¬ p3461) ∨ (¬ p4244) ∨ (¬ p4381) ∨ (¬ p5045))
    : (¬ p3105) ∨ p2761 ∨ p2870 ∨ (¬ p5045) ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h51121 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step86781 (p2459 p2619 p2870 p3146 p4244 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73540 : p4244 ∨ p2870)
    (h43949 : (¬ p2619) ∨ (¬ p3146) ∨ (¬ p4244) ∨ (¬ p4348))
    : (¬ p2619) ∨ p2459 ∨ p2870 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43949 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86782 (p2132 p2138 p2284 p2870 p2901 p3952 p4244 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73214 : p2138 ∨ p2132)
    (h73496 : p3952 ∨ p2284)
    (h45407 : (¬ p2138) ∨ (¬ p2901) ∨ (¬ p3952) ∨ (¬ p4244))
    : (¬ p2901) ∨ p2870 ∨ p2132 ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45407 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86783 (p2156 p2563 p2870 p3051 p3646 p4244 p4882 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73436 : p3646 ∨ p2156)
    (h51441 : (¬ p2563) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4244) ∨ (¬ p4882))
    : p2870 ∨ (¬ p3051) ∨ (¬ p4882) ∨ (¬ p2563) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4882 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51441 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86784 (p2132 p2138 p2331 p2870 p3246 p3461 p3506 p3690 p4191 p4244 p4421 p4621 p4786 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73446 : p3690 ∨ p3246)
    (h73540 : p4244 ∨ p2870)
    (h73214 : p2138 ∨ p2132)
    (h51253 : (¬ p2138) ∨ (¬ p2331) ∨ (¬ p3506) ∨ (¬ p3690) ∨ (¬ p4191) ∨ (¬ p4244) ∨ (¬ p4421) ∨ (¬ p4621) ∨ (¬ p4786))
    : (¬ p3506) ∨ p3461 ∨ p3246 ∨ (¬ p4786) ∨ (¬ p4421) ∨ (¬ p4621) ∨ p2870 ∨ p2132 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4421 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h51253 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step86786 (p2341 p2870 p2911 p3551 p3741 p4244 p4283 p4882 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73540 : p4244 ∨ p2870)
    (h49729 : (¬ p2911) ∨ (¬ p3551) ∨ (¬ p3741) ∨ (¬ p4244) ∨ (¬ p4283) ∨ (¬ p4882))
    : (¬ p2911) ∨ p2341 ∨ (¬ p4882) ∨ (¬ p3741) ∨ (¬ p4283) ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4882 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h49729 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step86787 (p2417 p2870 p3516 p3741 p3821 p4244 p4283 p4882 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73540 : p4244 ∨ p2870)
    (h55677 : (¬ p2417) ∨ (¬ p3741) ∨ (¬ p3821) ∨ (¬ p4244) ∨ (¬ p4283) ∨ (¬ p4882))
    : p3516 ∨ (¬ p2417) ∨ (¬ p3741) ∨ (¬ p4283) ∨ p2870 ∨ (¬ p4882) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4882 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55677 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step86788 (p2427 p2563 p2839 p2870 p3583 p4110 p4244 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73516 : p4110 ∨ p2563)
    (h73424 : p3583 ∨ p2839)
    (h64045 : (¬ p2427) ∨ (¬ p3583) ∨ (¬ p4110) ∨ (¬ p4244))
    : (¬ p2427) ∨ p2870 ∨ p2563 ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h64045 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86789 (p2619 p2870 p3550 p4244 p4441 p5559 p5660 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h51529 : (¬ p2619) ∨ (¬ p3550) ∨ (¬ p4244) ∨ (¬ p4441) ∨ (¬ p5559) ∨ (¬ p5660))
    : (¬ p5660) ∨ (¬ p4441) ∨ p2870 ∨ (¬ p2619) ∨ (¬ p3550) ∨ (¬ p5559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5660 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h51529 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step86790 (p2132 p2138 p2248 p2331 p2363 p2668 p2870 p3246 p3690 p3873 p4244 p4669 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73214 : p2138 ∨ p2132)
    (h73446 : p3690 ∨ p3246)
    (h58075 : (¬ p2138) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3690) ∨ (¬ p3873) ∨ (¬ p4244) ∨ (¬ p4669))
    : (¬ p2668) ∨ (¬ p3873) ∨ p2870 ∨ (¬ p4669) ∨ (¬ p2331) ∨ (¬ p2248) ∨ p2132 ∨ (¬ p2363) ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h58075 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step86796 (p2144 p2493 p2499 p2619 p2753 p2870 p3016 p3051 p3083 p4244 p4256 p4434 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73542 : p4256 ∨ p3083)
    (h73260 : p2499 ∨ p2493)
    (h71666 : (¬ p4256) ∨ (¬ p2619) ∨ (¬ p3016) ∨ (¬ p4434) ∨ (¬ p3051) ∨ (¬ p2499) ∨ (¬ p2144) ∨ (¬ p2753) ∨ (¬ p4244))
    : p2870 ∨ (¬ p2619) ∨ p3083 ∨ (¬ p4434) ∨ (¬ p3016) ∨ (¬ p3051) ∨ p2493 ∨ (¬ p2753) ∨ (¬ p2144) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h71666 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step86800 (p2132 p2138 p2246 p2528 p2651 p2744 p2870 p3083 p3246 p3366 p3690 p4244 p4669 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73446 : p3690 ∨ p3246)
    (h73540 : p4244 ∨ p2870)
    (h61625 : (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3366) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4669))
    : p2132 ∨ (¬ p2246) ∨ (¬ p2528) ∨ p3246 ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p4669) ∨ p2870 ∨ (¬ p3366) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h61625 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step86801 (p2132 p2138 p2241 p2247 p2744 p2870 p3246 p3366 p3399 p3527 p3690 p4244 p4666 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73446 : p3690 ∨ p3246)
    (h73214 : p2138 ∨ p2132)
    (h73540 : p4244 ∨ p2870)
    (h52963 : (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4666))
    : (¬ p3527) ∨ p2241 ∨ p3246 ∨ (¬ p2744) ∨ p2132 ∨ (¬ p4666) ∨ p2870 ∨ (¬ p3366) ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h52963 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step86802 (p2241 p2247 p2619 p2727 p2870 p3051 p3083 p4111 p4244 p4256 p4434 p4521 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73518 : p4111 ∨ p2727)
    (h73226 : p2247 ∨ p2241)
    (h73542 : p4256 ∨ p3083)
    (h62532 : (¬ p2247) ∨ (¬ p2619) ∨ (¬ p3051) ∨ (¬ p4111) ∨ (¬ p4244) ∨ (¬ p4256) ∨ (¬ p4434) ∨ (¬ p4521))
    : p2870 ∨ (¬ p2619) ∨ (¬ p4521) ∨ p2727 ∨ p2241 ∨ (¬ p4434) ∨ p3083 ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h62532 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step86803 (p2598 p2839 p2870 p3055 p3367 p3583 p4244 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73350 : p3055 ∨ p2598)
    (h73540 : p4244 ∨ p2870)
    (h60297 : (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p4244))
    : (¬ p3367) ∨ p2839 ∨ p2598 ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60297 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step86805 (p2573 p2870 p2946 p2952 p3366 p3461 p3519 p3564 p4236 p4244 p4376 p4831 p5051 p5660 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73540 : p4244 ∨ p2870)
    (h59773 : (¬ p2573) ∨ (¬ p2952) ∨ (¬ p3366) ∨ (¬ p3461) ∨ (¬ p3519) ∨ (¬ p3564) ∨ (¬ p4236) ∨ (¬ p4244) ∨ (¬ p4376) ∨ (¬ p4831) ∨ (¬ p5051) ∨ (¬ p5660))
    : (¬ p3461) ∨ (¬ p5660) ∨ (¬ p2573) ∨ p2946 ∨ (¬ p4376) ∨ (¬ p5051) ∨ (¬ p4831) ∨ (¬ p4236) ∨ (¬ p3366) ∨ p2870 ∨ (¬ p3564) ∨ (¬ p3519) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h59773 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u13))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u5))) (fun r10 => (False.elim (r10 u1)))))))))))))))))))))))))

theorem step86806 (p2144 p2598 p2870 p3051 p3055 p4244 p4884 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73350 : p3055 ∨ p2598)
    (h50084 : (¬ p2144) ∨ (¬ p3051) ∨ (¬ p3055) ∨ (¬ p4244) ∨ (¬ p4884))
    : p2870 ∨ (¬ p3051) ∨ p2598 ∨ (¬ p4884) ∨ (¬ p2144) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4884 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50084 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step86812 (p2156 p2166 p2220 p2870 p4120 p4244 p4418 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h73540 : p4244 ∨ p2870)
    (h54774 : (¬ p2156) ∨ (¬ p2166) ∨ (¬ p4120) ∨ (¬ p4244) ∨ (¬ p4418))
    : p2220 ∨ p2870 ∨ (¬ p2156) ∨ (¬ p2166) ∨ (¬ p4418) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2220) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h54774 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step86817 (p2427 p2870 p3054 p3422 p4244 p4717 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h64316 : (¬ p2427) ∨ (¬ p3054) ∨ (¬ p3422) ∨ (¬ p4244) ∨ (¬ p4717))
    : p2870 ∨ (¬ p3422) ∨ (¬ p4717) ∨ (¬ p3054) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3054 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h64316 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86820 (p2573 p2579 p2870 p3483 p3564 p3905 p3985 p4137 p4244 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73274 : p2579 ∨ p2573)
    (h73524 : p4137 ∨ p3564)
    (h56227 : (¬ p2579) ∨ (¬ p3483) ∨ (¬ p3905) ∨ (¬ p3985) ∨ (¬ p4137) ∨ (¬ p4244))
    : (¬ p3483) ∨ p2870 ∨ p2573 ∨ p3564 ∨ (¬ p3905) ∨ (¬ p3985) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3985 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56227 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step86821 (p2210 p2630 p2870 p2891 p4244 p4392 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h43881 : (¬ p2210) ∨ (¬ p2630) ∨ (¬ p2891) ∨ (¬ p4244) ∨ (¬ p4392))
    : p2870 ∨ (¬ p4392) ∨ (¬ p2891) ∨ (¬ p2630) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h43881 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step86823 (p2341 p3516 p3551 p3657 p3821 : Prop)
    (h73469 : (¬ p3516) ∨ (¬ p3821))
    (h73408 : p3551 ∨ p2341)
    (h15110 : (¬ p3551) ∨ (¬ p3657) ∨ p3821)
    : (¬ p3516) ∨ (¬ p3657) ∨ p2341 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3821) := (Or.elim h73469 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h15110 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u3 r1)))))))

theorem step86830 (p2341 p2881 p3516 p3551 p3631 p3817 : Prop)
    (h73468 : p3817 ∨ p3631)
    (h73408 : p3551 ∨ p2341)
    (h43692 : (¬ p2881) ∨ (¬ p3516) ∨ (¬ p3551) ∨ (¬ p3817))
    : p3631 ∨ (¬ p3516) ∨ p2341 ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43692 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86832 (p2881 p2996 p3027 p3246 p3516 p3690 p4066 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73340 : p3027 ∨ p2996)
    (h46023 : (¬ p2881) ∨ (¬ p3027) ∨ (¬ p3516) ∨ (¬ p3690) ∨ (¬ p4066))
    : p3246 ∨ p2996 ∨ (¬ p2881) ∨ (¬ p4066) ∨ (¬ p3516) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46023 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step86838 (p2177 p2341 p2417 p3516 p3551 p4276 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73408 : p3551 ∨ p2341)
    (h50379 : (¬ p2177) ∨ (¬ p3516) ∨ (¬ p3551) ∨ (¬ p4276) ∨ (¬ p4278))
    : p2417 ∨ (¬ p3516) ∨ (¬ p2177) ∨ p2341 ∨ (¬ p4276) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50379 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step86843 (p2417 p3516 p3575 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h20218 : (¬ p3516) ∨ (¬ p3575) ∨ (¬ p4278))
    : p2417 ∨ (¬ p3516) ∨ (¬ p3575) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h20218 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step86845 (p2417 p2470 p2476 p3516 p4278 p4922 p5201 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73250 : p2476 ∨ p2470)
    (h52521 : (¬ p2476) ∨ (¬ p3516) ∨ (¬ p4278) ∨ (¬ p4922) ∨ (¬ p5201))
    : p2417 ∨ (¬ p3516) ∨ (¬ p5201) ∨ (¬ p4922) ∨ p2470 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h52521 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86849 (p2341 p2417 p2881 p3516 p3551 p4277 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73408 : p3551 ∨ p2341)
    (h51925 : (¬ p2881) ∨ (¬ p3516) ∨ (¬ p3551) ∨ (¬ p4277) ∨ (¬ p4278))
    : (¬ p3516) ∨ p2417 ∨ (¬ p4277) ∨ p2341 ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h51925 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step86851 (p2417 p2441 p2870 p3516 p3691 p4278 p4885 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h57962 : (¬ p2441) ∨ (¬ p2870) ∨ (¬ p3516) ∨ (¬ p3691) ∨ (¬ p4278) ∨ (¬ p4885))
    : p2417 ∨ (¬ p3516) ∨ (¬ p3691) ∨ (¬ p4885) ∨ (¬ p2870) ∨ (¬ p2441) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h57962 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step86853 (p2901 p2960 p3246 p3516 p3690 p4320 p4988 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73552 : p4320 ∨ p2901)
    (h63865 : (¬ p2960) ∨ (¬ p3516) ∨ (¬ p3690) ∨ (¬ p4320) ∨ (¬ p4988))
    : (¬ p3516) ∨ p3246 ∨ (¬ p4988) ∨ (¬ p2960) ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63865 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86854 (p2220 p3246 p3516 p3690 p4120 p4204 p4988 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h73446 : p3690 ∨ p3246)
    (h69509 : (¬ p4120) ∨ (¬ p3690) ∨ (¬ p3516) ∨ (¬ p4204) ∨ (¬ p4988))
    : (¬ p3516) ∨ (¬ p4204) ∨ p2220 ∨ (¬ p4988) ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h69509 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step86859 (p2132 p2138 p2192 p2274 p2417 p2911 p3097 p3367 p3516 p3759 p4173 p4243 p4278 p4734 p5201 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73352 : p3097 ∨ p2274)
    (h72735 : p4734)
    (h73528 : p4173 ∨ p2192)
    (h73214 : p2138 ∨ p2132)
    (h50670 : (¬ p2138) ∨ (¬ p2911) ∨ (¬ p3097) ∨ (¬ p3367) ∨ (¬ p3516) ∨ (¬ p3759) ∨ (¬ p4173) ∨ (¬ p4243) ∨ (¬ p4278) ∨ (¬ p4734) ∨ (¬ p5201))
    : p2417 ∨ (¬ p2911) ∨ (¬ p4243) ∨ (¬ p3367) ∨ p2274 ∨ (¬ p5201) ∨ (¬ p3516) ∨ p2192 ∨ (¬ p3759) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p4734 := h72735;
    let u13 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u14 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h50670 (fun q0 => (False.elim (q0 u14))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (False.elim (r9 u5)))))))))))))))))))))))

theorem step86870 (p2417 p2922 p2928 p3516 p4278 p5194 p5201 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73320 : p2928 ∨ p2922)
    (h49408 : (¬ p2928) ∨ (¬ p3516) ∨ (¬ p4278) ∨ (¬ p5194) ∨ (¬ p5201))
    : p2417 ∨ (¬ p3516) ∨ p2922 ∨ (¬ p5194) ∨ (¬ p5201) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h49408 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step86876 (p2417 p2727 p2996 p3027 p3516 p4066 p4111 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73518 : p4111 ∨ p2727)
    (h73340 : p3027 ∨ p2996)
    (h64462 : (¬ p3027) ∨ (¬ p3516) ∨ (¬ p4066) ∨ (¬ p4111) ∨ (¬ p4278))
    : p2417 ∨ (¬ p3516) ∨ p2727 ∨ (¬ p4066) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h64462 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step86880 (p2881 p2951 p2992 p3246 p3516 p3690 p4988 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h46029 : (¬ p2881) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3516) ∨ (¬ p3690) ∨ (¬ p4988))
    : p3246 ∨ (¬ p4988) ∨ (¬ p3516) ∨ (¬ p2951) ∨ (¬ p2881) ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h46029 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step86881 (p2177 p2341 p3246 p3516 p3551 p3690 p4556 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73408 : p3551 ∨ p2341)
    (h49707 : (¬ p2177) ∨ (¬ p3516) ∨ (¬ p3551) ∨ (¬ p3690) ∨ (¬ p4556))
    : (¬ p3516) ∨ (¬ p4556) ∨ p3246 ∨ (¬ p2177) ∨ p2341 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49707 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step86885 (p2341 p3146 p3516 p3551 p3692 p4443 p4902 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73408 : p3551 ∨ p2341)
    (h65229 : (¬ p3516) ∨ (¬ p3551) ∨ (¬ p3692) ∨ (¬ p4443) ∨ (¬ p4902))
    : (¬ p3516) ∨ p3146 ∨ (¬ p4443) ∨ p2341 ∨ (¬ p4902) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4443 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h65229 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step86887 (p2319 p2396 p3309 p3516 p3549 p4107 p5022 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73406 : p3549 ∨ p3309)
    (h49423 : (¬ p2319) ∨ (¬ p3516) ∨ (¬ p3549) ∨ (¬ p4107) ∨ (¬ p5022))
    : (¬ p3516) ∨ p2396 ∨ (¬ p2319) ∨ (¬ p5022) ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5022 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49423 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step86893 (p2341 p2449 p2881 p3516 p3551 p3947 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73408 : p3551 ∨ p2341)
    (h43806 : (¬ p2881) ∨ (¬ p3516) ∨ (¬ p3551) ∨ (¬ p3947))
    : p2449 ∨ (¬ p3516) ∨ (¬ p2881) ∨ p2341 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43806 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86895 (p2341 p2528 p2534 p3516 p3551 p4420 p4443 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73408 : p3551 ∨ p2341)
    (h41204 : (¬ p2534) ∨ (¬ p3516) ∨ (¬ p3551) ∨ (¬ p4420) ∨ (¬ p4443))
    : (¬ p3516) ∨ p2528 ∨ (¬ p4443) ∨ p2341 ∨ (¬ p4420) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4443 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41204 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86898 (p2707 p2881 p3246 p3516 p3577 p3690 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h45770 : (¬ p2707) ∨ (¬ p2881) ∨ (¬ p3516) ∨ (¬ p3577) ∨ (¬ p3690))
    : p3246 ∨ (¬ p2707) ∨ (¬ p2881) ∨ (¬ p3577) ∨ (¬ p3516) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45770 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step86899 (p2230 p2440 p2542 p2589 p3246 p3516 p3690 p5201 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73270 : p2542 ∨ p2440)
    (h73284 : p2589 ∨ p2230)
    (h59185 : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3516) ∨ (¬ p3690) ∨ (¬ p5201))
    : (¬ p3516) ∨ p3246 ∨ (¬ p5201) ∨ p2440 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h59185 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86901 (p3246 p3516 p3690 p3691 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h5395 : (¬ p3516) ∨ (¬ p3690) ∨ (¬ p3691))
    : (¬ p3516) ∨ (¬ p3691) ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h5395 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step86902 (p2881 p2951 p3136 p3246 p3516 p3690 p4988 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h45772 : (¬ p2881) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p3516) ∨ (¬ p3690) ∨ (¬ p4988))
    : p3246 ∨ (¬ p4988) ∨ (¬ p2881) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p3516) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45772 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step86905 (p2427 p2995 p3246 p3516 p3690 p4066 p4235 p4705 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73536 : p4235 ∨ p2427)
    (h62140 : (¬ p2995) ∨ (¬ p3516) ∨ (¬ p3690) ∨ (¬ p4066) ∨ (¬ p4235) ∨ (¬ p4705))
    : (¬ p3516) ∨ p3246 ∨ (¬ p4066) ∨ (¬ p2995) ∨ (¬ p4705) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h62140 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step86906 (p2427 p3246 p3516 p3690 p4235 p4539 p4988 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73536 : p4235 ∨ p2427)
    (h50839 : (¬ p3516) ∨ (¬ p3690) ∨ (¬ p4235) ∨ (¬ p4539) ∨ (¬ p4988))
    : (¬ p3516) ∨ p3246 ∨ p2427 ∨ (¬ p4539) ∨ (¬ p4988) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4539 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50839 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step86910 (p2177 p2319 p2396 p2779 p2829 p3516 p4107 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h58232 : (¬ p2177) ∨ (¬ p2319) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (¬ p3516) ∨ (¬ p4107))
    : p2396 ∨ (¬ p3516) ∨ (¬ p2319) ∨ (¬ p2829) ∨ (¬ p2177) ∨ (¬ p2779) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2396) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2779 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h58232 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step86914 (p2143 p2427 p2563 p2630 p3051 p3556 p4110 p4392 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73516 : p4110 ∨ p2563)
    (h64224 : (¬ p2143) ∨ (¬ p2427) ∨ (¬ p2630) ∨ (¬ p3556) ∨ (¬ p4110) ∨ (¬ p4392))
    : p3051 ∨ (¬ p4392) ∨ (¬ p2630) ∨ (¬ p2427) ∨ (¬ p2143) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h64224 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step86921 (p2751 p2996 p3027 p3256 p3609 p4044 p4340 p4359 p4392 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h73340 : p3027 ∨ p2996)
    (h61899 : (¬ p2751) ∨ (¬ p3027) ∨ (¬ p3256) ∨ (¬ p4044) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4392))
    : p3609 ∨ (¬ p4044) ∨ (¬ p4359) ∨ p2996 ∨ (¬ p3256) ∨ (¬ p2751) ∨ (¬ p4392) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61899 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step86925 (p2143 p2751 p2901 p2992 p3051 p3556 p4392 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h53532 : (¬ p2143) ∨ (¬ p2751) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3556) ∨ (¬ p4392))
    : (¬ p2901) ∨ (¬ p2992) ∨ (¬ p4392) ∨ p3051 ∨ (¬ p2143) ∨ (¬ p2751) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53532 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step86927 (p2166 p2619 p3367 p3371 p3585 p3694 p4392 p4749 : Prop)
    (h73450 : p3694 ∨ p2619)
    (h73428 : p3585 ∨ p3367)
    (h58378 : (¬ p2166) ∨ (¬ p3371) ∨ (¬ p3585) ∨ (¬ p3694) ∨ (¬ p4392) ∨ (¬ p4749))
    : (¬ p3371) ∨ p2619 ∨ (¬ p4749) ∨ (¬ p4392) ∨ p3367 ∨ (¬ p2166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3371 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3694 := (Or.elim h73450 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h58378 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step86929 (p2192 p2860 p3367 p3371 p3585 p3758 p4392 p4749 : Prop)
    (h73456 : p3758 ∨ p2860)
    (h73428 : p3585 ∨ p3367)
    (h64364 : (¬ p2192) ∨ (¬ p3371) ∨ (¬ p3585) ∨ (¬ p3758) ∨ (¬ p4392) ∨ (¬ p4749))
    : p2860 ∨ (¬ p3371) ∨ p3367 ∨ (¬ p2192) ∨ (¬ p4749) ∨ (¬ p4392) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2860) := (fun h => hn (Or.inl h));
    let u1 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h64364 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step86930 (p2177 p2437 p2630 p2696 p3399 p3527 p3548 p4276 p4366 p4733 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73404 : p3548 ∨ p3527)
    (h58373 : (¬ p2177) ∨ (¬ p2437) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p3548) ∨ (¬ p4276) ∨ (¬ p4366) ∨ (¬ p4733))
    : p3399 ∨ (¬ p4733) ∨ p3527 ∨ (¬ p2177) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p4276) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h58373 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step86931 (p2440 p2542 p2563 p2630 p2696 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h42858 : (¬ p2542) ∨ (¬ p2563) ∨ (¬ p2630) ∨ (¬ p2696))
    : p2440 ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42858 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step86932 (p2427 p2440 p2542 p2630 p2696 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h52195 : (¬ p2427) ∨ (¬ p2542) ∨ (¬ p2630) ∨ (¬ p2696))
    : p2440 ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h52195 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step86934 (p2098 p2104 p2630 p2737 p3366 p4963 p5008 : Prop)
    (h73204 : p2104 ∨ p2098)
    (h49564 : (¬ p2104) ∨ (¬ p2630) ∨ (¬ p2737) ∨ (¬ p3366) ∨ (¬ p4963) ∨ (¬ p5008))
    : p2098 ∨ (¬ p3366) ∨ (¬ p2737) ∨ (¬ p5008) ∨ (¬ p2630) ∨ (¬ p4963) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5008 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49564 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step86937 (p2145 p2156 p2177 p2274 p2299 p2630 p2696 p3083 p3097 p3646 p4420 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73436 : p3646 ∨ p2156)
    (h73234 : p2299 ∨ p2177)
    (h48165 : (¬ p2145) ∨ (¬ p2299) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p3083) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4420))
    : (¬ p3083) ∨ p2274 ∨ (¬ p2145) ∨ p2156 ∨ p2177 ∨ (¬ p2696) ∨ (¬ p4420) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3083 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48165 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step86938 (p2295 p2331 p2630 p2651 p2657 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h54876 : (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2630) ∨ (¬ p2657))
    : (¬ p2295) ∨ (¬ p2331) ∨ p2651 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h54876 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step86939 (p2187 p2274 p2307 p2313 p2630 p2696 p2787 p3083 p3989 p4596 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73502 : p3989 ∨ p2187)
    (h62235 : (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2787) ∨ (¬ p3083) ∨ (¬ p3989) ∨ (¬ p4596))
    : (¬ p3083) ∨ p2307 ∨ (¬ p2630) ∨ (¬ p2787) ∨ (¬ p4596) ∨ p2187 ∨ (¬ p2274) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3083 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h62235 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step86940 (p2145 p2177 p2437 p2630 p2696 p2881 p3051 p3556 p3570 p4276 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73414 : p3556 ∨ p3051)
    (h41780 : (¬ p2145) ∨ (¬ p2177) ∨ (¬ p2437) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4276))
    : p2881 ∨ (¬ p2437) ∨ (¬ p2177) ∨ (¬ p2630) ∨ (¬ p2145) ∨ (¬ p4276) ∨ (¬ p2696) ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h41780 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step86942 (p2396 p2630 p2696 p3093 p3309 p3343 p3549 p3591 p4107 p4638 p4733 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73432 : p3591 ∨ p3093)
    (h73406 : p3549 ∨ p3309)
    (h50874 : (¬ p2630) ∨ (¬ p2696) ∨ (¬ p3343) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4107) ∨ (¬ p4638) ∨ (¬ p4733))
    : (¬ p3343) ∨ (¬ p4638) ∨ p2396 ∨ p3093 ∨ (¬ p2630) ∨ p3309 ∨ (¬ p4733) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4638 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h50874 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step86944 (p2630 p2651 p2657 p3286 p3506 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h46601 : (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3286) ∨ (¬ p3506))
    : (¬ p3286) ∨ (¬ p3506) ∨ (¬ p2630) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3286 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46601 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step86945 (p2264 p2630 p2651 p2657 p2685 p3553 p3572 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73410 : p3553 ∨ p2264)
    (h73420 : p3572 ∨ p2685)
    (h47140 : (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3553) ∨ (¬ p3572))
    : p2651 ∨ (¬ p2630) ∨ p2264 ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47140 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step86946 (p2528 p2534 p2630 p2651 p2657 p3005 p3877 p4437 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73268 : p2534 ∨ p2528)
    (h73288 : p2657 ∨ p2651)
    (h54967 : (¬ p2534) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3877) ∨ (¬ p4437))
    : p3005 ∨ p2528 ∨ (¬ p4437) ∨ (¬ p2630) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54967 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86952 (p2220 p2363 p2630 p2696 p2753 p3083 p3146 p3645 p3692 p4120 p4596 p4877 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73522 : p4120 ∨ p2220)
    (h62644 : (¬ p2363) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3083) ∨ (¬ p3645) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4596) ∨ (¬ p4877))
    : (¬ p2753) ∨ p3146 ∨ (¬ p2363) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p4877) ∨ (¬ p3645) ∨ p2220 ∨ (¬ p4596) ∨ (¬ p3083) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2753 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h62644 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step86953 (p2210 p2437 p2630 p2696 p2753 p3093 p3309 p3549 p3591 p4276 p4877 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73406 : p3549 ∨ p3309)
    (h63749 : (¬ p2210) ∨ (¬ p2437) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4276) ∨ (¬ p4877))
    : p3093 ∨ p3309 ∨ (¬ p2696) ∨ (¬ p2437) ∨ (¬ p2753) ∨ (¬ p4877) ∨ (¬ p4276) ∨ (¬ p2210) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3309) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h63749 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step86954 (p2331 p2630 p2651 p2657 p2668 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h47077 : (¬ p2331) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2668))
    : (¬ p2331) ∨ (¬ p2668) ∨ (¬ p2630) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47077 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step86957 (p2440 p2542 p2608 p2630 p2737 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h63861 : (¬ p2542) ∨ (¬ p2608) ∨ (¬ p2630) ∨ (¬ p2737))
    : p2440 ∨ (¬ p2630) ∨ (¬ p2737) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h63861 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step86958 (p2630 p2651 p2657 p3212 p3266 p3366 p3370 p3680 p3755 p4035 p4236 p4377 p4444 p4697 p5171 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73506 : p4035 ∨ p3755)
    (h73288 : p2657 ∨ p2651)
    (h63545 : (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3212) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3680) ∨ (¬ p4035) ∨ (¬ p4236) ∨ (¬ p4377) ∨ (¬ p4444) ∨ (¬ p4697) ∨ (¬ p5171))
    : (¬ p3370) ∨ p3266 ∨ (¬ p2630) ∨ (¬ p4377) ∨ (¬ p3680) ∨ (¬ p4236) ∨ (¬ p3366) ∨ (¬ p4697) ∨ p3755 ∨ p2651 ∨ (¬ p5171) ∨ (¬ p3212) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3370 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u13 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u14 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h63545 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u7))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step86962 (p2132 p2138 p2630 p2696 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h70260 : (¬ p2696) ∨ (¬ p2630) ∨ (¬ p2138))
    : p2132 ∨ (¬ p2630) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h70260 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step86965 (p2630 p2737 p2839 p3583 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h69660 : (¬ p3583) ∨ (¬ p2630) ∨ (¬ p2737))
    : (¬ p2737) ∨ p2839 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h69660 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u0)))))))

theorem step86966 (p2630 p2651 p2657 p2745 p2946 p2992 p3662 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73288 : p2657 ∨ p2651)
    (h56685 : (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2745) ∨ (¬ p2946) ∨ (¬ p3662))
    : p2992 ∨ (¬ p2946) ∨ (¬ p2745) ∨ p2651 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56685 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step86967 (p2331 p2440 p2542 p2553 p2630 p2737 p2963 p4236 p4715 p4734 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73270 : p2542 ∨ p2440)
    (h72735 : p4734)
    (h66735 : (¬ p2630) ∨ (¬ p2553) ∨ (¬ p2963) ∨ (¬ p4715) ∨ (¬ p2542) ∨ (¬ p4236) ∨ (¬ p2737) ∨ (¬ p4734))
    : (¬ p4236) ∨ (¬ p2737) ∨ p2331 ∨ (¬ p2553) ∨ (¬ p2630) ∨ p2440 ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4236 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u9 : p4734 := h72735;
    (Or.elim h66735 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u9)))))))))))))))))

theorem step86968 (p2630 p2651 p2657 p2737 p4236 p4734 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h72735 : p4734)
    (h42791 : (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2737) ∨ (¬ p4236) ∨ (¬ p4734))
    : (¬ p2737) ∨ (¬ p4236) ∨ p2651 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4734 := h72735;
    (Or.elim h42791 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step86970 (p2132 p2630 p2651 p2657 p4236 p5052 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h41008 : (¬ p2132) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p4236) ∨ (¬ p5052))
    : (¬ p4236) ∨ (¬ p2132) ∨ p2651 ∨ (¬ p2630) ∨ (¬ p5052) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4236 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5052 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41008 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step86972 (p2630 p2651 p2657 p2774 p2829 p3688 p4236 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73444 : p3688 ∨ p2829)
    (h53868 : (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2774) ∨ (¬ p3688) ∨ (¬ p4236))
    : (¬ p4236) ∨ (¬ p2630) ∨ (¬ p2774) ∨ p2651 ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4236 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h53868 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step86976 (p2630 p2651 p2657 p2774 p4236 p4845 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h53904 : (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2774) ∨ (¬ p4236) ∨ (¬ p4845))
    : (¬ p4236) ∨ (¬ p2774) ∨ (¬ p4845) ∨ p2651 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4236 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4845 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53904 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86977 (p2307 p2459 p2630 p2651 p2657 p2781 p2881 p3755 p4035 p4236 p4275 p5113 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h73288 : p2657 ∨ p2651)
    (h42407 : (¬ p2307) ∨ (¬ p2459) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2781) ∨ (¬ p2881) ∨ (¬ p4035) ∨ (¬ p4236) ∨ (¬ p4275) ∨ (¬ p5113))
    : (¬ p2307) ∨ p3755 ∨ (¬ p2459) ∨ (¬ p4275) ∨ (¬ p2881) ∨ (¬ p4236) ∨ (¬ p2781) ∨ (¬ p5113) ∨ (¬ p2630) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5113 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h42407 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step86981 (p2563 p2630 p2651 p2657 p2946 p4241 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h53404 : (¬ p2563) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p4241))
    : (¬ p2946) ∨ p2651 ∨ (¬ p4241) ∨ (¬ p2630) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h53404 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step86982 (p2284 p2630 p2651 p2657 p2946 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h46595 : (¬ p2284) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2946))
    : (¬ p2946) ∨ p2651 ∨ (¬ p2284) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46595 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step86984 (p2630 p2651 p2657 p2685 p2946 p3572 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73420 : p3572 ∨ p2685)
    (h44774 : (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3572))
    : p2651 ∨ (¬ p2946) ∨ p2685 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44774 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step86986 (p2630 p2651 p2657 p2946 p3156 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h46558 : (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3156))
    : (¬ p2946) ∨ p2651 ∨ (¬ p3156) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46558 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step86989 (p2187 p2331 p2630 p2668 p2963 p3324 p3361 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73386 : p3324 ∨ p2668)
    (h59495 : (¬ p2187) ∨ (¬ p2630) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3361))
    : p2331 ∨ (¬ p2630) ∨ p2668 ∨ (¬ p3361) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h59495 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step86990 (p2177 p2254 p2630 p2651 p2657 p3005 p3093 p3309 p3877 p4041 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73488 : p3877 ∨ p3005)
    (h49202 : (¬ p2177) ∨ (¬ p2254) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3877) ∨ (¬ p4041))
    : (¬ p3309) ∨ (¬ p4041) ∨ p2651 ∨ (¬ p2177) ∨ p3005 ∨ (¬ p2254) ∨ (¬ p2630) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49202 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step86991 (p2145 p2459 p2630 p2696 p2881 p3051 p3343 p3556 p3570 p4332 p4348 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73562 : p4348 ∨ p2459)
    (h73414 : p3556 ∨ p3051)
    (h42147 : (¬ p2145) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p3343) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4332) ∨ (¬ p4348))
    : p2881 ∨ p2459 ∨ (¬ p4332) ∨ (¬ p3343) ∨ (¬ p2630) ∨ p3051 ∨ (¬ p2145) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h42147 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u9)))))))))))))))))

theorem step86992 (p2459 p2470 p2528 p2630 p3519 p4116 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h48960 : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2630) ∨ (¬ p3519) ∨ (¬ p4116) ∨ (¬ p4348))
    : (¬ p2470) ∨ (¬ p3519) ∨ p2459 ∨ (¬ p2630) ∨ (¬ p2528) ∨ (¬ p4116) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48960 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step86993 (p2210 p2254 p2630 p2651 p2657 p2881 p2891 p3005 p3877 p4041 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73288 : p2657 ∨ p2651)
    (h60898 : (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3877) ∨ (¬ p4041))
    : (¬ p2891) ∨ (¬ p2881) ∨ (¬ p2630) ∨ (¬ p2210) ∨ (¬ p2254) ∨ p3005 ∨ (¬ p4041) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u9 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h60898 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step86998 (p2331 p2553 p2630 p2651 p2657 p3984 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h46315 : (¬ p2331) ∨ (¬ p2553) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3984))
    : (¬ p2331) ∨ (¬ p2553) ∨ (¬ p2630) ∨ p2651 ∨ (¬ p3984) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46315 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step87000 (p2331 p2630 p2797 p2946 p2952 p4195 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73330 : p2952 ∨ p2946)
    (h69661 : (¬ p2331) ∨ (¬ p4195) ∨ (¬ p2952) ∨ (¬ p2630))
    : p2797 ∨ (¬ p2331) ∨ p2946 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h69661 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step87003 (p2177 p2341 p2630 p2685 p3551 p3572 p4155 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73420 : p3572 ∨ p2685)
    (h51365 : (¬ p2177) ∨ (¬ p2630) ∨ (¬ p3551) ∨ (¬ p3572) ∨ (¬ p4155))
    : p2341 ∨ (¬ p4155) ∨ (¬ p2177) ∨ (¬ p2630) ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51365 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step87007 (p2449 p2630 p2651 p2657 p2807 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h46603 : (¬ p2449) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2807))
    : p2651 ∨ (¬ p2449) ∨ (¬ p2630) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h46603 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step87008 (p2630 p2651 p2657 p2745 p2807 p2996 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h56469 : (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2745) ∨ (¬ p2807) ∨ (¬ p2996))
    : (¬ p2996) ∨ p2651 ∨ (¬ p2807) ∨ (¬ p2745) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h56469 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step87011 (p2331 p2630 p2685 p2807 p2963 p3572 p4972 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73420 : p3572 ∨ p2685)
    (h52692 : (¬ p2630) ∨ (¬ p2807) ∨ (¬ p2963) ∨ (¬ p3572) ∨ (¬ p4972))
    : p2331 ∨ (¬ p4972) ∨ (¬ p2630) ∨ p2685 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h52692 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step87013 (p2630 p2651 p2657 p3166 p3256 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h61284 : (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3166) ∨ (¬ p3256))
    : (¬ p3166) ∨ (¬ p3256) ∨ p2651 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h61284 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step87020 (p2088 p2363 p2630 p3005 p3177 p3857 p3877 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73480 : p3857 ∨ p2088)
    (h43982 : (¬ p2363) ∨ (¬ p2630) ∨ (¬ p3177) ∨ (¬ p3857) ∨ (¬ p3877))
    : p3005 ∨ p2088 ∨ (¬ p2630) ∨ (¬ p2363) ∨ (¬ p3177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2088) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43982 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step87022 (p2352 p2630 p3019 p3323 p3564 p4137 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h52705 : (¬ p2352) ∨ (¬ p2630) ∨ (¬ p3019) ∨ (¬ p3323) ∨ (¬ p4137))
    : p3564 ∨ (¬ p3019) ∨ (¬ p3323) ∨ (¬ p2630) ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h52705 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step87023 (p2459 p2630 p3005 p3256 p3877 p4118 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h73488 : p3877 ∨ p3005)
    (h47715 : (¬ p2459) ∨ (¬ p2630) ∨ (¬ p3877) ∨ (¬ p4118))
    : p3256 ∨ p3005 ∨ (¬ p2459) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47715 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step87025 (p2264 p2630 p2651 p2657 p2807 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h46260 : (¬ p2264) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2807))
    : p2651 ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h46260 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step87028 (p2440 p2542 p2630 p3286 p3755 p4035 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73506 : p4035 ∨ p3755)
    (h61382 : (¬ p2542) ∨ (¬ p2630) ∨ (¬ p3286) ∨ (¬ p4035))
    : (¬ p3286) ∨ p2440 ∨ p3755 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3286 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h61382 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step87031 (p2563 p2630 p2651 p2657 p2797 p3745 p4195 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73288 : p2657 ∨ p2651)
    (h48831 : (¬ p2563) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3745) ∨ (¬ p4195))
    : p2797 ∨ p2651 ∨ (¬ p2563) ∨ (¬ p2630) ∨ (¬ p3745) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h48831 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step87032 (p2274 p2284 p2630 p3097 p3136 p3952 p4315 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73352 : p3097 ∨ p2274)
    (h73496 : p3952 ∨ p2284)
    (h60242 : (¬ p2630) ∨ (¬ p3097) ∨ (¬ p3952) ∨ (¬ p4315))
    : p3136 ∨ p2274 ∨ p2284 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h60242 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step87033 (p2274 p2284 p2630 p2748 p2992 p3097 p3662 p3952 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73352 : p3097 ∨ p2274)
    (h73496 : p3952 ∨ p2284)
    (h60241 : (¬ p2630) ∨ (¬ p2748) ∨ (¬ p3097) ∨ (¬ p3662) ∨ (¬ p3952))
    : p2992 ∨ p2274 ∨ p2284 ∨ (¬ p2748) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h60241 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step87035 (p2493 p2630 p2797 p4195 p4389 p4814 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h40965 : (¬ p2493) ∨ (¬ p2630) ∨ (¬ p4195) ∨ (¬ p4389) ∨ (¬ p4814))
    : p2797 ∨ (¬ p4389) ∨ (¬ p2493) ∨ (¬ p2630) ∨ (¬ p4814) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h40965 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step87036 (p2553 p2588 p2630 p2651 p2657 p2797 p4195 p4389 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73288 : p2657 ∨ p2651)
    (h73282 : p2588 ∨ p2553)
    (h45432 : (¬ p2588) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p4195) ∨ (¬ p4389))
    : p2797 ∨ p2651 ∨ p2553 ∨ (¬ p4389) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45432 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step87037 (p2573 p2630 p2665 p2797 p4195 p4389 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h48362 : (¬ p2573) ∨ (¬ p2630) ∨ (¬ p2665) ∨ (¬ p4195) ∨ (¬ p4389))
    : p2797 ∨ (¬ p4389) ∨ (¬ p2573) ∨ (¬ p2665) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48362 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step87039 (p2437 p2630 p2797 p4195 p4389 p4711 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h62668 : (¬ p2437) ∨ (¬ p2630) ∨ (¬ p4195) ∨ (¬ p4389) ∨ (¬ p4711))
    : (¬ p2437) ∨ (¬ p4389) ∨ (¬ p4711) ∨ (¬ p2630) ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4711 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62668 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step87042 (p2156 p2563 p2630 p2656 p2982 p4110 p4399 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h62870 : (¬ p2156) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2982) ∨ (¬ p4110) ∨ (¬ p4399))
    : (¬ p2982) ∨ (¬ p4399) ∨ (¬ p2656) ∨ p2563 ∨ (¬ p2156) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62870 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step87046 (p2373 p2427 p2630 p2656 p3051 p4235 p4399 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h46338 : (¬ p2373) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p3051) ∨ (¬ p4235) ∨ (¬ p4399))
    : (¬ p3051) ∨ (¬ p2373) ∨ (¬ p4399) ∨ (¬ p2630) ∨ (¬ p2656) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h46338 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step87052 (p2156 p2252 p2274 p2396 p2630 p2651 p2657 p2741 p3370 p3755 p4035 p4377 p4641 p5171 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h73288 : p2657 ∨ p2651)
    (h42399 : (¬ p2156) ∨ (¬ p2252) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2741) ∨ (¬ p3370) ∨ (¬ p4035) ∨ (¬ p4377) ∨ (¬ p4641) ∨ (¬ p5171))
    : (¬ p2396) ∨ p3755 ∨ (¬ p4377) ∨ (¬ p2156) ∨ (¬ p5171) ∨ (¬ p2274) ∨ (¬ p2252) ∨ p2651 ∨ (¬ p4641) ∨ (¬ p2630) ∨ (¬ p2741) ∨ (¬ p3370) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u13 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h42399 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u8))) (fun r10 => (False.elim (r10 u4)))))))))))))))))))))))))

theorem step87059 (p2187 p2274 p2307 p2630 p2651 p2657 p2781 p3005 p3097 p3877 p4236 p4774 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73488 : p3877 ∨ p3005)
    (h73288 : p2657 ∨ p2651)
    (h63539 : (¬ p2187) ∨ (¬ p2307) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2781) ∨ (¬ p3097) ∨ (¬ p3877) ∨ (¬ p4236) ∨ (¬ p4774))
    : p2274 ∨ p3005 ∨ (¬ p2630) ∨ (¬ p4774) ∨ p2651 ∨ (¬ p4236) ∨ (¬ p2781) ∨ (¬ p2307) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63539 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step87061 (p2553 p2630 p2797 p3016 p4195 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h51929 : (¬ p2553) ∨ (¬ p2630) ∨ (¬ p3016) ∨ (¬ p4195))
    : p2797 ∨ (¬ p2553) ∨ (¬ p2630) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h51929 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step87062 (p2295 p2553 p2630 p2797 p3568 p4195 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73532 : p4195 ∨ p2797)
    (h43997 : (¬ p2553) ∨ (¬ p2630) ∨ (¬ p3568) ∨ (¬ p4195))
    : p2295 ∨ p2797 ∨ (¬ p2553) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2295) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43997 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step87064 (p2274 p2553 p2573 p2630 p2656 p3097 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h47377 : (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p3097))
    : (¬ p2553) ∨ (¬ p2656) ∨ p2274 ∨ (¬ p2630) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47377 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step87065 (p2470 p2528 p2630 p2656 p3146 p3692 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h63309 : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p3692))
    : (¬ p2528) ∨ p3146 ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2470) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h63309 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step87067 (p2470 p2630 p2665 p3005 p3877 p4437 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h49150 : (¬ p2470) ∨ (¬ p2630) ∨ (¬ p2665) ∨ (¬ p3877) ∨ (¬ p4437))
    : p3005 ∨ (¬ p2470) ∨ (¬ p2630) ∨ (¬ p2665) ∨ (¬ p4437) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49150 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step87068 (p2470 p2630 p2665 p3005 p3877 p4437 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h62820 : (¬ p2470) ∨ (¬ p2630) ∨ (¬ p2665) ∨ (¬ p3877) ∨ (¬ p4437))
    : p3005 ∨ (¬ p2470) ∨ (¬ p4437) ∨ (¬ p2665) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h62820 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step87069 (p2363 p2470 p2528 p2630 p2656 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h62999 : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p4347))
    : p2363 ∨ (¬ p2470) ∨ (¬ p2656) ∨ (¬ p2630) ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h62999 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step87070 (p2630 p2665 p2685 p3389 p3572 p3740 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h48973 : (¬ p2630) ∨ (¬ p2665) ∨ (¬ p3389) ∨ (¬ p3572) ∨ (¬ p3740))
    : p2685 ∨ (¬ p3389) ∨ (¬ p2630) ∨ (¬ p2665) ∨ (¬ p3740) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2685) := (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48973 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step87072 (p2220 p2264 p2459 p2630 p2656 p2807 p3414 p3553 p3969 p4348 p4399 p5122 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h73392 : p3414 ∨ p2807)
    (h73562 : p4348 ∨ p2459)
    (h71672 : (¬ p3969) ∨ (¬ p3553) ∨ (¬ p4348) ∨ (¬ p2220) ∨ (¬ p3414) ∨ (¬ p2656) ∨ (¬ p4399) ∨ (¬ p2630) ∨ (¬ p5122))
    : (¬ p3969) ∨ p2264 ∨ (¬ p5122) ∨ (¬ p2220) ∨ (¬ p2630) ∨ (¬ p2656) ∨ p2807 ∨ (¬ p4399) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2264) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h71672 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step87074 (p2373 p2630 p2656 p2982 p3212 p4399 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h46928 : (¬ p2373) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p3212) ∨ (¬ p4399) ∨ (¬ p4948))
    : p2982 ∨ (¬ p4399) ∨ (¬ p2373) ∨ (¬ p3212) ∨ (¬ p2630) ∨ (¬ p2656) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h46928 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step87075 (p2230 p2406 p2630 p2656 p2745 p3238 p3402 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h49336 : (¬ p2230) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2745) ∨ (¬ p3238) ∨ (¬ p3402))
    : p2406 ∨ (¬ p3402) ∨ (¬ p2745) ∨ (¬ p2630) ∨ (¬ p2230) ∨ (¬ p2656) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2406) := (fun h => hn (Or.inl h));
    let u1 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49336 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step87076 (p2230 p2630 p2656 p2685 p3572 p3740 p4644 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h61891 : (¬ p2230) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p3572) ∨ (¬ p3740) ∨ (¬ p4644))
    : p2685 ∨ (¬ p2656) ∨ (¬ p2630) ∨ (¬ p4644) ∨ (¬ p3740) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2685) := (fun h => hn (Or.inl h));
    let u1 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h61891 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step87078 (p2331 p2470 p2630 p2656 p2963 p3323 p3461 p4037 p4149 p4191 p5119 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73508 : p4037 ∨ p3323)
    (h73338 : p2963 ∨ p2331)
    (h71674 : (¬ p4149) ∨ (¬ p2470) ∨ (¬ p4037) ∨ (¬ p5119) ∨ (¬ p2656) ∨ (¬ p2963) ∨ (¬ p4191) ∨ (¬ p2630))
    : (¬ p4149) ∨ p3461 ∨ (¬ p2630) ∨ p3323 ∨ (¬ p2656) ∨ (¬ p5119) ∨ p2331 ∨ (¬ p2470) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4149 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h71674 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step87080 (p2563 p2630 p2982 p3212 p3519 p4116 p4399 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h47071 : (¬ p2563) ∨ (¬ p2630) ∨ (¬ p3212) ∨ (¬ p3519) ∨ (¬ p4116) ∨ (¬ p4399) ∨ (¬ p4948))
    : p2982 ∨ (¬ p4116) ∨ (¬ p2630) ∨ (¬ p2563) ∨ (¬ p4399) ∨ (¬ p3212) ∨ (¬ p3519) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h47071 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u7)))))))))))))))

theorem step87089 (p2437 p2630 p2745 p2922 p2928 p3402 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h48371 : (¬ p2437) ∨ (¬ p2630) ∨ (¬ p2745) ∨ (¬ p2928) ∨ (¬ p3402))
    : (¬ p3402) ∨ (¬ p2437) ∨ (¬ p2745) ∨ p2922 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3402 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48371 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step87092 (p2630 p2748 p3073 p3256 p4261 p4262 p5008 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h49255 : (¬ p2630) ∨ (¬ p2748) ∨ (¬ p3256) ∨ (¬ p4261) ∨ (¬ p4262) ∨ (¬ p5008))
    : p3073 ∨ (¬ p4262) ∨ (¬ p5008) ∨ (¬ p3256) ∨ (¬ p2748) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p4262 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5008 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49255 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step87096 (p2220 p2373 p2563 p2630 p2951 p3413 p3880 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h46337 : (¬ p2220) ∨ (¬ p2563) ∨ (¬ p2630) ∨ (¬ p2951) ∨ (¬ p3413) ∨ (¬ p3880))
    : p2373 ∨ (¬ p2220) ∨ (¬ p2563) ∨ (¬ p3413) ∨ (¬ p2951) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2373) := (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h46337 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step87101 (p2608 p2630 p2685 p3037 p3399 p3572 p3954 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73420 : p3572 ∨ p2685)
    (h47487 : (¬ p2630) ∨ (¬ p3037) ∨ (¬ p3399) ∨ (¬ p3572) ∨ (¬ p3954))
    : (¬ p3037) ∨ p2608 ∨ (¬ p2630) ∨ p2685 ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3037 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47487 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step87104 (p2630 p2685 p2922 p3572 p3575 p4155 p4814 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h49857 : (¬ p2630) ∨ (¬ p2922) ∨ (¬ p3572) ∨ (¬ p3575) ∨ (¬ p4155) ∨ (¬ p4814))
    : (¬ p2922) ∨ (¬ p4155) ∨ (¬ p3575) ∨ (¬ p4814) ∨ (¬ p2630) ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h49857 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step87107 (p2241 p2630 p2992 p3136 p4315 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h44900 : (¬ p2241) ∨ (¬ p2630) ∨ (¬ p2992) ∨ (¬ p4315))
    : (¬ p2992) ∨ (¬ p2241) ∨ p3136 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44900 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step87108 (p2630 p2992 p3016 p3136 p4315 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h47476 : (¬ p2630) ∨ (¬ p2992) ∨ (¬ p3016) ∨ (¬ p4315))
    : p3136 ∨ (¬ p2992) ∨ (¬ p3016) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h47476 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step87109 (p2440 p2542 p2630 p3005 p3189 p3877 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73488 : p3877 ∨ p3005)
    (h46475 : (¬ p2542) ∨ (¬ p2630) ∨ (¬ p3189) ∨ (¬ p3877))
    : (¬ p3189) ∨ p2440 ∨ (¬ p2630) ∨ p3005 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46475 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step87110 (p2241 p2630 p2748 p3399 p4319 p4366 p4452 p4972 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h57235 : (¬ p2241) ∨ (¬ p2630) ∨ (¬ p2748) ∨ (¬ p4319) ∨ (¬ p4366) ∨ (¬ p4452) ∨ (¬ p4972))
    : (¬ p4319) ∨ p3399 ∨ (¬ p2241) ∨ (¬ p2630) ∨ (¬ p4452) ∨ (¬ p4972) ∨ (¬ p2748) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h57235 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step87111 (p2630 p2655 p3193 p3222 p3346 p4116 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h71675 : (¬ p3222) ∨ (¬ p3346) ∨ (¬ p4116) ∨ (¬ p2630) ∨ (¬ p2655))
    : p3193 ∨ (¬ p3346) ∨ (¬ p4116) ∨ (¬ p2630) ∨ (¬ p2655) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h71675 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step87114 (p2210 p2630 p2797 p3093 p3555 p3922 p4195 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73532 : p4195 ∨ p2797)
    (h50194 : (¬ p2630) ∨ (¬ p3093) ∨ (¬ p3555) ∨ (¬ p3922) ∨ (¬ p4195))
    : (¬ p3093) ∨ p2210 ∨ (¬ p3922) ∨ p2797 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3093 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50194 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step87117 (p2630 p3399 p3755 p3830 p3853 p4035 p4366 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73506 : p4035 ∨ p3755)
    (h55321 : (¬ p2630) ∨ (¬ p3830) ∨ (¬ p3853) ∨ (¬ p4035) ∨ (¬ p4366))
    : p3399 ∨ (¬ p3853) ∨ p3755 ∨ (¬ p3830) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p3853 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h55321 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step87118 (p2192 p2563 p2630 p2957 p3136 p3370 p4173 p4315 : Prop)
    (h73528 : p4173 ∨ p2192)
    (h73550 : p4315 ∨ p3136)
    (h49832 : (¬ p2563) ∨ (¬ p2630) ∨ (¬ p2957) ∨ (¬ p3370) ∨ (¬ p4173) ∨ (¬ p4315))
    : (¬ p2957) ∨ (¬ p3370) ∨ p2192 ∨ p3136 ∨ (¬ p2563) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2957 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49832 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step87119 (p2630 p2797 p2810 p4194 p4195 : Prop)
    (h73531 : (¬ p2797) ∨ (¬ p4195))
    (h73316 : p2810 ∨ p2630)
    (h6286 : (¬ p2810) ∨ (¬ p4194) ∨ p4195)
    : (¬ p2797) ∨ (¬ p4194) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4195) := (Or.elim h73531 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h6286 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u3 r1)))))))

theorem step87121 (p2797 p3136 p4153 p4195 p4315 : Prop)
    (h73531 : (¬ p2797) ∨ (¬ p4195))
    (h73550 : p4315 ∨ p3136)
    (h22979 : (¬ p4153) ∨ p4195 ∨ (¬ p4315))
    : (¬ p2797) ∨ (¬ p4153) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4195) := (Or.elim h73531 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h22979 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step87123 (p2797 p3005 p3877 p4195 p4341 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73531 : (¬ p2797) ∨ (¬ p4195))
    (h25210 : (¬ p3877) ∨ p4195 ∨ (¬ p4341))
    : (¬ p4341) ∨ p3005 ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : (¬ p4195) := (Or.elim h73531 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h25210 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step87124 (p2553 p2685 p2797 p3572 p4195 p4973 : Prop)
    (h73531 : (¬ p2797) ∨ (¬ p4195))
    (h73420 : p3572 ∨ p2685)
    (h66895 : p4195 ∨ (¬ p4973) ∨ (¬ p2553) ∨ (¬ p3572))
    : (¬ p2553) ∨ (¬ p2797) ∨ p2685 ∨ (¬ p4973) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4195) := (Or.elim h73531 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u5 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h66895 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step87125 (p2685 p2797 p3572 p4156 p4195 : Prop)
    (h73531 : (¬ p2797) ∨ (¬ p4195))
    (h73420 : p3572 ∨ p2685)
    (h6577 : (¬ p3572) ∨ (¬ p4156) ∨ p4195)
    : (¬ p4156) ∨ (¬ p2797) ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4195) := (Or.elim h73531 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u4 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h6577 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u3 r1)))))))

theorem step87129 (p2797 p4844 p4845 : Prop)
    (h73788 : p4844 ∨ (¬ p2797))
    (h7954 : (¬ p4844) ∨ p4845)
    : (¬ p2797) ∨ p4845 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4845) := (fun h => hn (Or.inr h));
    let u2 : p4844 := (Or.elim h73788 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h7954 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step87130 (p2797 p4844 p4846 : Prop)
    (h73788 : p4844 ∨ (¬ p2797))
    (h7955 : (¬ p4844) ∨ p4846)
    : (¬ p2797) ∨ p4846 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4846) := (fun h => hn (Or.inr h));
    let u2 : p4844 := (Or.elim h73788 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h7955 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step87134 (p2295 p2696 p2737 p2743 p2829 p3589 p4328 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h43061 : (¬ p2295) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p2829) ∨ (¬ p3589) ∨ (¬ p4328))
    : p2737 ∨ (¬ p2829) ∨ (¬ p3589) ∨ (¬ p2295) ∨ (¬ p2696) ∨ (¬ p4328) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h43061 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step87141 (p2122 p2220 p2331 p2373 p2396 p2963 p2982 p3366 p3519 p3822 p3880 p4107 p4236 p4328 p4376 p4395 p4399 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73514 : p4107 ∨ p2396)
    (h73490 : p3880 ∨ p2373)
    (h73472 : p3822 ∨ p2122)
    (h63568 : (¬ p2220) ∨ (¬ p2963) ∨ (¬ p2982) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3822) ∨ (¬ p3880) ∨ (¬ p4107) ∨ (¬ p4236) ∨ (¬ p4328) ∨ (¬ p4376) ∨ (¬ p4395) ∨ (¬ p4399))
    : p2331 ∨ (¬ p4328) ∨ (¬ p4399) ∨ (¬ p3519) ∨ (¬ p4236) ∨ (¬ p3366) ∨ p2396 ∨ (¬ p4395) ∨ (¬ p2982) ∨ (¬ p2220) ∨ p2373 ∨ (¬ p4376) ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u14 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u15 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    let u16 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u12 r0))));
    (Or.elim h63568 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u16))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u15))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u14))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u1))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u11))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u7))) (fun r11 => (False.elim (r11 u2)))))))))))))))))))))))))))

theorem step87143 (p2630 p2696 p2774 p2810 p3365 p4328 p4975 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73390 : p3365 ∨ p2696)
    (h51062 : (¬ p2774) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p4328) ∨ (¬ p4975))
    : (¬ p2774) ∨ (¬ p4328) ∨ (¬ p4975) ∨ p2630 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2774 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51062 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step87148 (p3323 p3917 p4037 p4328 : Prop)
    (h73507 : (¬ p3323) ∨ (¬ p4037))
    (h26088 : (¬ p3917) ∨ p4037 ∨ (¬ p4328))
    : (¬ p3917) ∨ (¬ p3323) ∨ (¬ p4328) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3917 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4037) := (Or.elim h73507 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h26088 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step87153 (p2122 p2396 p3246 p3822 p3872 p4107 p4328 p4564 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73472 : p3822 ∨ p2122)
    (h62272 : (¬ p3246) ∨ (¬ p3822) ∨ (¬ p3872) ∨ (¬ p4107) ∨ (¬ p4328) ∨ (¬ p4564))
    : (¬ p3246) ∨ (¬ p4328) ∨ p2396 ∨ p2122 ∨ (¬ p3872) ∨ (¬ p4564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62272 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step87156 (p2122 p2295 p3568 p3822 p4328 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73415 : (¬ p2295) ∨ (¬ p3568))
    (h25390 : p3568 ∨ (¬ p3822) ∨ (¬ p4328))
    : p2122 ∨ (¬ p2295) ∨ (¬ p4328) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p3568) := (Or.elim h73415 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h25390 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step87157 (p2274 p2295 p2829 p2839 p3097 p3583 p4328 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73352 : p3097 ∨ p2274)
    (h54259 : (¬ p2295) ∨ (¬ p2829) ∨ (¬ p3097) ∨ (¬ p3583) ∨ (¬ p4328))
    : (¬ p2829) ∨ (¬ p4328) ∨ p2839 ∨ p2274 ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54259 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step87163 (p2651 p2657 p2737 p2743 p2829 p3361 p4328 p4975 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73288 : p2657 ∨ p2651)
    (h50226 : (¬ p2657) ∨ (¬ p2743) ∨ (¬ p2829) ∨ (¬ p3361) ∨ (¬ p4328) ∨ (¬ p4975))
    : (¬ p2829) ∨ p2737 ∨ (¬ p4328) ∨ p2651 ∨ (¬ p3361) ∨ (¬ p4975) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50226 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step87165 (p2156 p2630 p2810 p2860 p2957 p3646 p4313 p4704 : Prop)
    (h73046 : p4704)
    (h73316 : p2810 ∨ p2630)
    (h73436 : p3646 ∨ p2156)
    (h41376 : (¬ p2810) ∨ (¬ p2860) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p4313) ∨ (¬ p4704))
    : (¬ p2957) ∨ (¬ p4313) ∨ (¬ p2860) ∨ p2630 ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2957 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4704 := h73046;
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41376 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step87166 (p2619 p2630 p2810 p3156 p3497 p4313 p4704 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73046 : p4704)
    (h73400 : p3497 ∨ p3156)
    (h62441 : (¬ p2619) ∨ (¬ p2810) ∨ (¬ p3497) ∨ (¬ p4313) ∨ (¬ p4704))
    : (¬ p4313) ∨ (¬ p2619) ∨ p2630 ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4704 := h73046;
    let u6 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62441 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step87167 (p2220 p2619 p2630 p2810 p2957 p4120 p4313 p4704 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h73316 : p2810 ∨ p2630)
    (h73046 : p4704)
    (h41221 : (¬ p2619) ∨ (¬ p2810) ∨ (¬ p2957) ∨ (¬ p4120) ∨ (¬ p4313) ∨ (¬ p4704))
    : (¬ p2619) ∨ p2220 ∨ (¬ p4313) ∨ p2630 ∨ (¬ p2957) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4704 := h73046;
    (Or.elim h41221 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step87172 (p2696 p2753 p2839 p3583 p4313 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h30101 : (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3583) ∨ (¬ p4313))
    : p2839 ∨ (¬ p2753) ∨ (¬ p4313) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2839) := (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h30101 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step87173 (p2630 p2810 p3105 p3115 p4208 p4313 p4704 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73534 : p4208 ∨ p3115)
    (h73046 : p4704)
    (h41749 : (¬ p2810) ∨ (¬ p3105) ∨ (¬ p4208) ∨ (¬ p4313) ∨ (¬ p4704))
    : (¬ p4313) ∨ (¬ p3105) ∨ p2630 ∨ p3115 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p4704 := h73046;
    (Or.elim h41749 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step87176 (p2737 p2839 p3583 p4313 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h20349 : (¬ p2737) ∨ (¬ p3583) ∨ (¬ p4313))
    : (¬ p4313) ∨ p2839 ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h20349 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u0)))))))

theorem step87183 (p2685 p2870 p3572 p3699 p4244 p4313 : Prop)
    (h73539 : (¬ p2870) ∨ (¬ p4244))
    (h73420 : p3572 ∨ p2685)
    (h28860 : (¬ p3572) ∨ (¬ p3699) ∨ p4244 ∨ (¬ p4313))
    : (¬ p2870) ∨ (¬ p3699) ∨ p2685 ∨ (¬ p4313) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3699 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p4244) := (Or.elim h73539 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u5 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h28860 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step87188 (p2156 p2745 p2860 p2957 p2992 p3646 p3662 p4313 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73436 : p3646 ∨ p2156)
    (h41345 : (¬ p2745) ∨ (¬ p2860) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3662) ∨ (¬ p4313))
    : p2992 ∨ (¬ p4313) ∨ (¬ p2745) ∨ (¬ p2860) ∨ (¬ p2957) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41345 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step87193 (p2797 p2870 p2957 p3051 p3556 p4195 p4313 p4700 p4972 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73414 : p3556 ∨ p3051)
    (h64052 : (¬ p2870) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p4195) ∨ (¬ p4313) ∨ (¬ p4700) ∨ (¬ p4972))
    : p2797 ∨ (¬ p2957) ∨ (¬ p4313) ∨ (¬ p4972) ∨ (¬ p2870) ∨ (¬ p4700) ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h64052 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step87195 (p2727 p2745 p3105 p3115 p4111 p4208 p4313 p4700 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73534 : p4208 ∨ p3115)
    (h56560 : (¬ p2745) ∨ (¬ p3105) ∨ (¬ p4111) ∨ (¬ p4208) ∨ (¬ p4313) ∨ (¬ p4700))
    : (¬ p3105) ∨ p2727 ∨ (¬ p2745) ∨ (¬ p4700) ∨ p3115 ∨ (¬ p4313) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56560 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step87197 (p2641 p2727 p3019 p4111 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73517 : (¬ p2727) ∨ (¬ p4111))
    (h29593 : (¬ p3019) ∨ p4111 ∨ (¬ p4154))
    : p2641 ∨ (¬ p3019) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p4111) := (Or.elim h73517 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h29593 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step87202 (p2331 p2651 p2963 p3019 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h25605 : (¬ p2651) ∨ (¬ p2963) ∨ (¬ p3019))
    : p2331 ∨ (¬ p3019) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h25605 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step87208 (p2440 p2668 p2819 p2829 p3019 p3688 p4358 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73564 : p4358 ∨ p2819)
    (h54252 : (¬ p2440) ∨ (¬ p2668) ∨ (¬ p3019) ∨ (¬ p3688) ∨ (¬ p4358))
    : (¬ p2668) ∨ p2829 ∨ (¬ p3019) ∨ (¬ p2440) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54252 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step87210 (p2383 p2387 p2668 p2946 p3019 p3983 p4704 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h73046 : p4704)
    (h48152 : (¬ p2387) ∨ (¬ p2668) ∨ (¬ p2946) ∨ (¬ p3019) ∨ (¬ p3983) ∨ (¬ p4704))
    : (¬ p2668) ∨ (¬ p3983) ∨ (¬ p3019) ∨ p2383 ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3983 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p4704 := h73046;
    (Or.elim h48152 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step87213 (p2383 p2387 p2668 p2807 p3019 p3983 p4652 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h42379 : (¬ p2387) ∨ (¬ p2668) ∨ (¬ p2807) ∨ (¬ p3019) ∨ (¬ p3983) ∨ (¬ p4652))
    : (¬ p2668) ∨ (¬ p3983) ∨ (¬ p3019) ∨ p2383 ∨ (¬ p2807) ∨ (¬ p4652) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3983 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42379 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step87214 (p2553 p2630 p3019 p3564 p3567 p3654 p4137 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h46639 : (¬ p2553) ∨ (¬ p2630) ∨ (¬ p3019) ∨ (¬ p3567) ∨ (¬ p3654) ∨ (¬ p4137))
    : (¬ p3654) ∨ p3564 ∨ (¬ p3019) ∨ (¬ p3567) ∨ (¬ p2630) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46639 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step87216 (p2630 p2797 p2810 p3019 p4195 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73315 : (¬ p2630) ∨ (¬ p2810))
    (h40436 : p2810 ∨ (¬ p3019) ∨ (¬ p4195))
    : (¬ p3019) ∨ p2797 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3019 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : (¬ p2810) := (Or.elim h73315 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h40436 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u3)))))))

theorem step87222 (p2440 p2668 p3019 p3093 p3591 p3923 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h43945 : (¬ p2440) ∨ (¬ p2668) ∨ (¬ p3019) ∨ (¬ p3591) ∨ (¬ p3923))
    : p3093 ∨ (¬ p2668) ∨ (¬ p3019) ∨ (¬ p2440) ∨ (¬ p3923) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h43945 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step87223 (p2295 p2437 p3019 p3742 p3921 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h20174 : (¬ p2295) ∨ (¬ p3019) ∨ (¬ p3742) ∨ (¬ p3921))
    : (¬ p3019) ∨ (¬ p2295) ∨ p2437 ∨ (¬ p3921) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3019 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20174 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step87228 (p2608 p3366 p4735 : Prop)
    (h73734 : p4735 ∨ (¬ p2608))
    (h7685 : p3366 ∨ (¬ p4735))
    : p3366 ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3366) := (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4735 := (Or.elim h73734 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h7685 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step87229 (p2608 p3366 p5885 : Prop)
    (h74187 : (¬ p2608) ∨ (¬ p5885))
    (h12297 : p3366 ∨ p5885)
    : p3366 ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3366) := (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5885) := (Or.elim h74187 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12297 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step87257 (p2881 p4119 p4900 : Prop)
    (h73818 : p4900 ∨ p2881)
    (h8084 : p4119 ∨ (¬ p4900))
    : p4119 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4119) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr h));
    let u2 : p4900 := (Or.elim h73818 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h8084 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step87258 (p2881 p4119 p5941 : Prop)
    (h74261 : p2881 ∨ (¬ p5941))
    (h12632 : p4119 ∨ p5941)
    : p4119 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4119) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5941) := (Or.elim h74261 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12632 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step87263 (p2493 p2503 p2507 : Prop)
    (h73264 : p2503 ∨ (¬ p2493))
    (h3143 : (¬ p2503) ∨ p2507)
    : (¬ p2493) ∨ p2507 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2507) := (fun h => hn (Or.inr h));
    let u2 : p2503 := (Or.elim h73264 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h3143 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step87265 (p2727 p4116 p5911 : Prop)
    (h74221 : p2727 ∨ (¬ p5911))
    (h12448 : p4116 ∨ p5911)
    : p4116 ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4116) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5911) := (Or.elim h74221 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12448 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step87271 (p2230 p2589 p3389 p3540 p3741 : Prop)
    (h73283 : (¬ p2230) ∨ (¬ p2589))
    (h73402 : p3540 ∨ p3389)
    (h38156 : p2589 ∨ (¬ p3540) ∨ (¬ p3741))
    : (¬ p3741) ∨ (¬ p2230) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3741 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2589) := (Or.elim h73283 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u4 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h38156 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u0)))))))

theorem step87274 (p2187 p2563 p3051 p3989 p4109 p4110 p4140 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h73516 : p4110 ∨ p2563)
    (h71688 : (¬ p3989) ∨ (¬ p4109) ∨ (¬ p3051) ∨ (¬ p4140) ∨ (¬ p4110))
    : (¬ p4140) ∨ (¬ p3051) ∨ (¬ p4109) ∨ p2187 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4140 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h71688 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step87276 (p2241 p2459 p2470 p2476 p2528 p2534 p2992 p3156 p4902 p5193 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h73268 : p2534 ∨ p2528)
    (h58845 : (¬ p2241) ∨ (¬ p2459) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2992) ∨ (¬ p3156) ∨ (¬ p4902) ∨ (¬ p5193))
    : (¬ p2992) ∨ p2470 ∨ (¬ p2459) ∨ (¬ p2241) ∨ p2528 ∨ (¬ p3156) ∨ (¬ p4902) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2470) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h58845 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step87277 (p3379 p3449 p3452 p3453 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h4989 : (¬ p3449) ∨ (¬ p3452) ∨ (¬ p3453))
    : (¬ p3449) ∨ (¬ p3453) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3453 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h4989 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step87278 (p2470 p2528 p3073 p3453 p4261 p5194 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h58139 : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3453) ∨ (¬ p4261) ∨ (¬ p5194))
    : (¬ p2470) ∨ p3073 ∨ (¬ p2528) ∨ (¬ p3453) ∨ (¬ p5194) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3453 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h58139 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step87282 (p2406 p2528 p3073 p3453 p4261 p4608 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h49121 : (¬ p2406) ∨ (¬ p2528) ∨ (¬ p3453) ∨ (¬ p4261) ∨ (¬ p4608))
    : p3073 ∨ (¬ p2406) ∨ (¬ p3453) ∨ (¬ p2528) ∨ (¬ p4608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3453 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49121 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step87285 (p2563 p4203 p5879 : Prop)
    (h74179 : (¬ p2563) ∨ (¬ p5879))
    (h12263 : p4203 ∨ p5879)
    : p4203 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4203) := (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5879) := (Or.elim h74179 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12263 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step87286 (p2406 p2504 p2505 p2573 p2579 p3238 p3389 p4646 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73374 : p3238 ∨ p2406)
    (h44823 : (¬ p2504) ∨ (¬ p2505) ∨ (¬ p2579) ∨ (¬ p3238) ∨ (¬ p3389) ∨ (¬ p4646))
    : (¬ p3389) ∨ p2573 ∨ (¬ p2504) ∨ (¬ p4646) ∨ p2406 ∨ (¬ p2505) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h44823 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step87290 (p2307 p2313 p2505 p2785 p3016 p3309 p3574 p4390 p4814 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73238 : p2313 ∨ p2307)
    (h50754 : (¬ p2313) ∨ (¬ p2505) ∨ (¬ p2785) ∨ (¬ p3309) ∨ (¬ p3574) ∨ (¬ p4390) ∨ (¬ p4814))
    : (¬ p3309) ∨ p3016 ∨ (¬ p2785) ∨ (¬ p4390) ∨ p2307 ∨ (¬ p4814) ∨ (¬ p2505) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50754 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step87296 (p2386 p2406 p2505 p3238 p3319 p3654 p3946 p4717 : Prop)
    (h73492 : p3946 ∨ p3654)
    (h73374 : p3238 ∨ p2406)
    (h41659 : (¬ p2386) ∨ (¬ p2505) ∨ (¬ p3238) ∨ (¬ p3319) ∨ (¬ p3946) ∨ (¬ p4717))
    : (¬ p3319) ∨ p3654 ∨ (¬ p2386) ∨ (¬ p4717) ∨ (¬ p2505) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3654) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41659 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step87298 (p2504 p2505 p3422 p3584 p3590 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h29426 : (¬ p2504) ∨ (¬ p2505) ∨ (¬ p3584) ∨ (¬ p3590))
    : p3422 ∨ (¬ p3590) ∨ (¬ p2505) ∨ (¬ p2504) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h29426 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step87305 (p2307 p2504 p2584 p2665 p3016 p3309 p3549 p3574 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h73422 : p3574 ∨ p3016)
    (h54035 : (¬ p2307) ∨ (¬ p2504) ∨ (¬ p2584) ∨ (¬ p2665) ∨ (¬ p3549) ∨ (¬ p3574))
    : (¬ p2307) ∨ p3309 ∨ p3016 ∨ (¬ p2504) ∨ (¬ p2584) ∨ (¬ p2665) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3309) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h54035 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step87306 (p2504 p2573 p2579 p3093 p4108 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h20064 : (¬ p2504) ∨ (¬ p2579) ∨ (¬ p3093) ∨ (¬ p4108))
    : (¬ p4108) ∨ p2573 ∨ (¬ p3093) ∨ (¬ p2504) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4108 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h20064 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step87308 (p2504 p3319 p3564 p4026 : Prop)
    (h73504 : p4026 ∨ p3319)
    (h13948 : (¬ p2504) ∨ (¬ p3564) ∨ (¬ p4026))
    : p3319 ∨ (¬ p3564) ∨ (¬ p2504) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3319) := (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h13948 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step87310 (p2504 p2553 p3309 p3549 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h5167 : (¬ p2504) ∨ (¬ p2553) ∨ (¬ p3549))
    : p3309 ∨ (¬ p2553) ∨ (¬ p2504) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3309) := (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h5167 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step87311 (p2352 p2504 p3309 p3549 p3955 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h34221 : (¬ p2352) ∨ (¬ p2504) ∨ (¬ p3549) ∨ (¬ p3955))
    : (¬ p2504) ∨ p3309 ∨ (¬ p3955) ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2504 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3309) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h34221 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step87316 (p2241 p2247 p2440 p2504 p2542 p3016 p3449 p3574 p4371 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73270 : p2542 ∨ p2440)
    (h73422 : p3574 ∨ p3016)
    (h58544 : (¬ p2247) ∨ (¬ p2504) ∨ (¬ p2542) ∨ (¬ p3449) ∨ (¬ p3574) ∨ (¬ p4371))
    : p2241 ∨ (¬ p3449) ∨ (¬ p2504) ∨ (¬ p4371) ∨ p2440 ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u8 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h58544 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step87317 (p2406 p3093 p3238 p3379 p3452 p4717 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73374 : p3238 ∨ p2406)
    (h69189 : (¬ p3452) ∨ (¬ p3093) ∨ (¬ p4717) ∨ (¬ p3238))
    : p3379 ∨ (¬ p3093) ∨ p2406 ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h69189 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step87318 (p2504 p3016 p3093 p3379 p3452 p3574 p4814 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73422 : p3574 ∨ p3016)
    (h50439 : (¬ p2504) ∨ (¬ p3093) ∨ (¬ p3452) ∨ (¬ p3574) ∨ (¬ p4814))
    : (¬ p3093) ∨ p3379 ∨ p3016 ∨ (¬ p2504) ∨ (¬ p4814) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3093 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50439 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step87319 (p2504 p3093 p3379 p3422 p3452 p3584 p5217 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73426 : p3584 ∨ p3422)
    (h51580 : (¬ p2504) ∨ (¬ p3093) ∨ (¬ p3452) ∨ (¬ p3584) ∨ (¬ p5217))
    : (¬ p3093) ∨ p3379 ∨ p3422 ∨ (¬ p5217) ∨ (¬ p2504) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3093 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5217 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h51580 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step87321 (p2363 p2383 p2387 p2504 p3016 p3204 p3266 p3574 p4347 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73560 : p4347 ∨ p2363)
    (h73246 : p2387 ∨ p2383)
    (h73422 : p3574 ∨ p3016)
    (h45059 : (¬ p2387) ∨ (¬ p2504) ∨ (¬ p3204) ∨ (¬ p3574) ∨ (¬ p4347) ∨ (¬ p4444))
    : p3266 ∨ p2363 ∨ p2383 ∨ p3016 ∨ (¬ p3204) ∨ (¬ p2504) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45059 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step87329 (p3189 p5074 p6001 : Prop)
    (h74337 : p3189 ∨ (¬ p6001))
    (h12997 : p5074 ∨ p6001)
    : p5074 ∨ p3189 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5074) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6001) := (Or.elim h74337 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12997 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step87331 (p3309 p4427 p6022 : Prop)
    (h74361 : p3309 ∨ (¬ p6022))
    (h13127 : p4427 ∨ p6022)
    : p4427 ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4427) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3309) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6022) := (Or.elim h74361 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13127 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step87332 (p3093 p3399 p3591 p4427 p4435 p5472 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h42003 : (¬ p3399) ∨ (¬ p3591) ∨ p4427 ∨ (¬ p4435) ∨ (¬ p5472))
    : (¬ p4435) ∨ p4427 ∨ (¬ p3399) ∨ (¬ p5472) ∨ p3093 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4435 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5472 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42003 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step87333 (p2177 p4138 p4500 : Prop)
    (h73602 : p4500 ∨ p2177)
    (h7055 : p4138 ∨ (¬ p4500))
    : p4138 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4138) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2177) := (fun h => hn (Or.inr h));
    let u2 : p4500 := (Or.elim h73602 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h7055 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step87334 (p2177 p4138 p5797 : Prop)
    (h74073 : p2177 ∨ (¬ p5797))
    (h11783 : p4138 ∨ p5797)
    : p4138 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4138) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2177) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5797) := (Or.elim h74073 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11783 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step87337 (p2470 p2476 p2663 p3166 p3172 p4437 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h73249 : (¬ p2470) ∨ (¬ p2476))
    (h23348 : p2476 ∨ (¬ p2663) ∨ (¬ p3172) ∨ (¬ p4437))
    : p3166 ∨ (¬ p2470) ∨ (¬ p4437) ∨ (¬ p2663) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : (¬ p2476) := (Or.elim h73249 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h23348 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step87342 (p2493 p2499 p2641 p3402 p3984 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h35531 : (¬ p2499) ∨ (¬ p2641) ∨ (¬ p3402) ∨ (¬ p3984))
    : (¬ p2641) ∨ (¬ p3402) ∨ (¬ p3984) ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h35531 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step87343 (p2493 p2499 p2507 p3402 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h48067 : (¬ p2499) ∨ p2507 ∨ (¬ p3402))
    : p2507 ∨ (¬ p3402) ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2507) := (fun h => hn (Or.inl h));
    let u1 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48067 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step87348 (p2241 p2247 p3379 p3402 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h4899 : (¬ p2247) ∨ (¬ p3379) ∨ (¬ p3402))
    : p2241 ∨ (¬ p3402) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h4899 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u1)))))))

theorem step87357 (p2922 p2928 p3093 p3389 p3402 p3591 p4079 p4756 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73432 : p3591 ∨ p3093)
    (h48191 : (¬ p2928) ∨ (¬ p3389) ∨ (¬ p3402) ∨ (¬ p3591) ∨ (¬ p4079) ∨ (¬ p4756))
    : p2922 ∨ (¬ p3389) ∨ (¬ p4756) ∨ (¬ p4079) ∨ p3093 ∨ (¬ p3402) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4756 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48191 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step87360 (p2493 p2499 p2573 p2630 p2656 p2745 p3402 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h41104 : (¬ p2499) ∨ (¬ p2573) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2745) ∨ (¬ p3402))
    : (¬ p3402) ∨ (¬ p2573) ∨ p2493 ∨ (¬ p2656) ∨ (¬ p2745) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3402 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41104 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step87361 (p2132 p2138 p2748 p2922 p2928 p3362 p3389 p3402 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73320 : p2928 ∨ p2922)
    (h67296 : (¬ p2928) ∨ (¬ p3402) ∨ (¬ p2748) ∨ (¬ p3362) ∨ (¬ p2138) ∨ (¬ p3389))
    : (¬ p3402) ∨ p2132 ∨ (¬ p3389) ∨ (¬ p3362) ∨ p2922 ∨ (¬ p2748) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3402 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h67296 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step87363 (p2284 p2406 p2427 p2901 p3238 p3402 p3952 p4235 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73496 : p3952 ∨ p2284)
    (h73374 : p3238 ∨ p2406)
    (h46896 : (¬ p2901) ∨ (¬ p3238) ∨ (¬ p3402) ∨ (¬ p3952) ∨ (¬ p4235))
    : (¬ p2901) ∨ p2427 ∨ p2284 ∨ (¬ p3402) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46896 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step87365 (p2255 p2437 p2651 p2922 p2928 p3402 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h49657 : (¬ p2255) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2928) ∨ (¬ p3402))
    : p2922 ∨ (¬ p2437) ∨ (¬ p3402) ∨ (¬ p2255) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49657 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step87370 (p2696 p3425 p3471 p4781 : Prop)
    (h73395 : (¬ p3425) ∨ (¬ p3471))
    (h24452 : (¬ p2696) ∨ p3471 ∨ (¬ p4781))
    : (¬ p3425) ∨ (¬ p2696) ∨ (¬ p4781) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3425 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3471) := (Or.elim h73395 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    (Or.elim h24452 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step87373 (p2685 p4780 p4782 : Prop)
    (h73756 : p4780 ∨ (¬ p2685))
    (h7795 : (¬ p4780) ∨ p4782)
    : (¬ p2685) ∨ p4782 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2685 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4782) := (fun h => hn (Or.inr h));
    let u2 : p4780 := (Or.elim h73756 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h7795 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step87375 (p2685 p2737 p2807 p3414 p4780 : Prop)
    (h73392 : p3414 ∨ p2807)
    (h73756 : p4780 ∨ (¬ p2685))
    (h66890 : (¬ p4780) ∨ (¬ p2737) ∨ (¬ p3414))
    : p2807 ∨ (¬ p2737) ∨ (¬ p2685) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2807) := (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p4780 := (Or.elim h73756 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h66890 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step87379 (p2230 p2850 p3346 p3422 p3684 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h64678 : (¬ p2230) ∨ (¬ p3346) ∨ (¬ p3422) ∨ (¬ p3684))
    : p2850 ∨ (¬ p2230) ∨ (¬ p3346) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h64678 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step87380 (p2177 p2230 p2299 p2553 p2573 p2579 p2588 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h73282 : p2588 ∨ p2553)
    (h73274 : p2579 ∨ p2573)
    (h45310 : (¬ p2230) ∨ (¬ p2299) ∨ (¬ p2579) ∨ (¬ p2588))
    : (¬ p2230) ∨ p2177 ∨ p2553 ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2177) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45310 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step87385 (p2132 p2138 p2230 p2274 p2563 p3362 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h48948 : (¬ p2138) ∨ (¬ p2230) ∨ (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3362))
    : (¬ p2274) ∨ (¬ p2230) ∨ p2132 ∨ (¬ p2563) ∨ (¬ p3362) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48948 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step87387 (p2187 p2230 p2352 p2563 p3956 : Prop)
    (h73500 : p3956 ∨ p2352)
    (h46351 : (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3956))
    : (¬ p2187) ∨ (¬ p2563) ∨ (¬ p2230) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46351 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step87392 (p2230 p2553 p2573 p2579 p2588 p2850 p3684 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73274 : p2579 ∨ p2573)
    (h73282 : p2588 ∨ p2553)
    (h45316 : (¬ p2230) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3684))
    : p2850 ∨ (¬ p2230) ∨ p2573 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45316 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step87393 (p2230 p2573 p2579 p3660 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h5345 : (¬ p2230) ∨ (¬ p2579) ∨ (¬ p3660))
    : (¬ p3660) ∨ (¬ p2230) ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3660 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h5345 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u0)))))))

theorem step87394 (p2230 p2427 p2573 p2579 p3096 p4558 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h49566 : (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2579) ∨ (¬ p3096) ∨ (¬ p4558))
    : (¬ p2427) ∨ p2573 ∨ (¬ p4558) ∨ (¬ p3096) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h49566 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step87396 (p2230 p2427 p2573 p2579 p3016 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h53381 : (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2579) ∨ (¬ p3016))
    : (¬ p2427) ∨ p2573 ∨ (¬ p3016) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h53381 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step87398 (p2230 p2573 p2579 p2727 p3016 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h58865 : (¬ p2230) ∨ (¬ p2579) ∨ (¬ p2727) ∨ (¬ p3016))
    : (¬ p3016) ∨ p2573 ∨ (¬ p2230) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3016 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h58865 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step87403 (p2230 p2573 p2579 p2982 p3096 p5046 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h49338 : (¬ p2230) ∨ (¬ p2579) ∨ (¬ p2982) ∨ (¬ p3096) ∨ (¬ p5046))
    : (¬ p2982) ∨ (¬ p2230) ∨ (¬ p3096) ∨ p2573 ∨ (¬ p5046) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5046 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49338 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step87404 (p2230 p2373 p2573 p2579 p3096 p4509 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h49943 : (¬ p2230) ∨ (¬ p2373) ∨ (¬ p2579) ∨ (¬ p3096) ∨ (¬ p4509))
    : (¬ p2373) ∨ p2573 ∨ (¬ p4509) ∨ (¬ p3096) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h49943 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step87406 (p2187 p2230 p2406 p2573 p2579 p3096 p3238 p3989 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h73274 : p2579 ∨ p2573)
    (h73502 : p3989 ∨ p2187)
    (h43114 : (¬ p2230) ∨ (¬ p2579) ∨ (¬ p3096) ∨ (¬ p3238) ∨ (¬ p3989))
    : p2406 ∨ (¬ p2230) ∨ (¬ p3096) ∨ p2573 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2406) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43114 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step87407 (p2230 p2284 p2573 p2579 p3096 p4705 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h41152 : (¬ p2230) ∨ (¬ p2284) ∨ (¬ p2579) ∨ (¬ p3096) ∨ (¬ p4705))
    : (¬ p2284) ∨ (¬ p2230) ∨ (¬ p4705) ∨ (¬ p3096) ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41152 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step87408 (p2192 p2230 p2573 p2579 p3096 p4632 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h55100 : (¬ p2192) ∨ (¬ p2230) ∨ (¬ p2579) ∨ (¬ p3096) ∨ (¬ p4632))
    : (¬ p2192) ∨ (¬ p2230) ∨ (¬ p3096) ∨ p2573 ∨ (¬ p4632) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55100 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step87410 (p2187 p2230 p2352 p2573 p2579 p3956 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73500 : p3956 ∨ p2352)
    (h62261 : (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2579) ∨ (¬ p3956))
    : p2573 ∨ (¬ p2230) ∨ (¬ p2187) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62261 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step87412 (p2230 p2406 p2553 p2573 p2579 p2588 p3238 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h73274 : p2579 ∨ p2573)
    (h73282 : p2588 ∨ p2553)
    (h42930 : (¬ p2230) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3238))
    : p2406 ∨ (¬ p2230) ∨ p2573 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2406) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42930 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step87413 (p2230 p2573 p2579 p2901 p3096 p3879 p4558 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h51614 : (¬ p2230) ∨ (¬ p2579) ∨ (¬ p2901) ∨ (¬ p3096) ∨ (¬ p3879) ∨ (¬ p4558))
    : (¬ p2901) ∨ p2573 ∨ (¬ p3879) ∨ (¬ p2230) ∨ (¬ p3096) ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h51614 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step87415 (p2230 p2440 p2459 p2911 p3389 p3540 p3644 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73402 : p3540 ∨ p3389)
    (h73434 : p3644 ∨ p2911)
    (h61754 : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4348))
    : (¬ p2230) ∨ p2459 ∨ p3389 ∨ p2911 ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61754 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step87416 (p2230 p2440 p2553 p2573 p2579 p2588 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73282 : p2588 ∨ p2553)
    (h45356 : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2579) ∨ (¬ p2588))
    : (¬ p2230) ∨ p2573 ∨ (¬ p2440) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45356 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step87420 (p2230 p2440 p2573 p2579 p3564 p4137 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73524 : p4137 ∨ p3564)
    (h60643 : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2579) ∨ (¬ p4137))
    : (¬ p2230) ∨ p2573 ∨ p3564 ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h60643 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step87421 (p2230 p2440 p2881 p3389 p3540 p3570 p4001 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73402 : p3540 ∨ p3389)
    (h47645 : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p3540) ∨ (¬ p3570) ∨ (¬ p4001))
    : (¬ p2230) ∨ p2881 ∨ (¬ p4001) ∨ p3389 ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47645 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step87424 (p2230 p2440 p2922 p3389 p3540 p4281 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h52548 : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2922) ∨ (¬ p3540) ∨ (¬ p4281))
    : (¬ p2922) ∨ (¬ p2230) ∨ (¬ p4281) ∨ p3389 ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h52548 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step87430 (p2230 p2406 p3238 p3276 p3346 p4425 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h73578 : p4425 ∨ p3276)
    (h43089 : (¬ p2230) ∨ (¬ p3238) ∨ (¬ p3346) ∨ (¬ p4425))
    : p2406 ∨ p3276 ∨ (¬ p3346) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2406) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43089 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step87435 (p2230 p2406 p2493 p3238 p3389 p3540 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h73402 : p3540 ∨ p3389)
    (h43417 : (¬ p2230) ∨ (¬ p2493) ∨ (¬ p3238) ∨ (¬ p3540))
    : p2406 ∨ (¬ p2230) ∨ (¬ p2493) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2406) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43417 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step87438 (p2230 p2406 p2470 p2476 p2493 p3238 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h73250 : p2476 ∨ p2470)
    (h43140 : (¬ p2230) ∨ (¬ p2476) ∨ (¬ p2493) ∨ (¬ p3238))
    : p2406 ∨ (¬ p2230) ∨ (¬ p2493) ∨ p2470 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2406) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43140 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step87445 (p2230 p2373 p2470 p2476 p4434 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h65225 : (¬ p2230) ∨ (¬ p2373) ∨ (¬ p2476) ∨ (¬ p4434))
    : (¬ p2373) ∨ (¬ p2230) ∨ p2470 ∨ (¬ p4434) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h65225 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step87446 (p2230 p2459 p2911 p3389 p3540 p3644 p4348 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73562 : p4348 ∨ p2459)
    (h73402 : p3540 ∨ p3389)
    (h47660 : (¬ p2230) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4348))
    : p2911 ∨ p2459 ∨ p3389 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47660 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step87447 (p2230 p2850 p2911 p3389 p3540 p3644 p3684 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73434 : p3644 ∨ p2911)
    (h73402 : p3540 ∨ p3389)
    (h46872 : (¬ p2230) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p3684))
    : p2850 ∨ (¬ p2230) ∨ p2911 ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46872 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step87448 (p2177 p2230 p2573 p2579 p2911 p3581 p3644 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73274 : p2579 ∨ p2573)
    (h52484 : (¬ p2177) ∨ (¬ p2230) ∨ (¬ p2579) ∨ (¬ p3581) ∨ (¬ p3644))
    : p2911 ∨ (¬ p2177) ∨ p2573 ∨ (¬ p2230) ∨ (¬ p3581) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52484 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step87449 (p2230 p2573 p2579 p2630 p3016 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h47278 : (¬ p2230) ∨ (¬ p2579) ∨ (¬ p2630) ∨ (¬ p3016))
    : (¬ p2230) ∨ (¬ p3016) ∨ p2573 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47278 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step87450 (p2177 p2230 p2299 p2406 p2934 p3238 p3527 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h73374 : p3238 ∨ p2406)
    (h43425 : (¬ p2230) ∨ (¬ p2299) ∨ (¬ p2934) ∨ (¬ p3238) ∨ (¬ p3527))
    : (¬ p3527) ∨ (¬ p2934) ∨ p2177 ∨ p2406 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2934 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43425 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step87452 (p2230 p2331 p2363 p2668 p2870 p2963 p3246 p3324 p3362 p3698 p3950 p4347 p4789 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h73560 : p4347 ∨ p2363)
    (h73338 : p2963 ∨ p2331)
    (h64688 : (¬ p2230) ∨ (¬ p2870) ∨ (¬ p2963) ∨ (¬ p3246) ∨ (¬ p3324) ∨ (¬ p3362) ∨ (¬ p3698) ∨ (¬ p3950) ∨ (¬ p4347) ∨ (¬ p4789))
    : (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3698) ∨ p2668 ∨ (¬ p4789) ∨ (¬ p3362) ∨ (¬ p2230) ∨ p2363 ∨ (¬ p3950) ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h64688 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step87454 (p2230 p2363 p2383 p2387 p2440 p2577 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73246 : p2387 ∨ p2383)
    (h57118 : (¬ p2230) ∨ (¬ p2387) ∨ (¬ p2440) ∨ (¬ p2577) ∨ (¬ p4347))
    : (¬ p2230) ∨ (¬ p2577) ∨ p2363 ∨ p2383 ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h57118 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step87458 (p2230 p2850 p3246 p3389 p3540 p3684 p3690 p4001 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73402 : p3540 ∨ p3389)
    (h73446 : p3690 ∨ p3246)
    (h43486 : (¬ p2230) ∨ (¬ p3540) ∨ (¬ p3684) ∨ (¬ p3690) ∨ (¬ p4001))
    : p2850 ∨ (¬ p2230) ∨ p3389 ∨ p3246 ∨ (¬ p4001) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43486 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step87459 (p2230 p2440 p2470 p2476 p3146 p3692 p3693 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73250 : p2476 ∨ p2470)
    (h64476 : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2476) ∨ (¬ p3692) ∨ (¬ p3693))
    : (¬ p2230) ∨ p3146 ∨ p2470 ∨ (¬ p3693) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h64476 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step87460 (p2230 p2470 p2476 p2528 p2534 p2850 p3684 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73250 : p2476 ∨ p2470)
    (h73268 : p2534 ∨ p2528)
    (h54776 : (¬ p2230) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3684))
    : p2850 ∨ (¬ p2230) ∨ p2470 ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54776 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step87461 (p2230 p2440 p2470 p2476 p2528 p2534 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h73268 : p2534 ∨ p2528)
    (h60015 : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2476) ∨ (¬ p2534))
    : (¬ p2230) ∨ p2470 ∨ (¬ p2440) ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2470) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60015 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step87468 (p2230 p2459 p2470 p2476 p2528 p2534 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73250 : p2476 ∨ p2470)
    (h62232 : (¬ p2230) ∨ (¬ p2459) ∨ (¬ p2476) ∨ (¬ p2534))
    : (¬ p2230) ∨ p2528 ∨ p2470 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h62232 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step87475 (p2187 p2230 p2470 p2476 p2563 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h42918 : (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2476) ∨ (¬ p2563))
    : (¬ p2187) ∨ p2470 ∨ (¬ p2563) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2470) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42918 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step87477 (p2230 p2406 p2470 p2476 p3083 p3238 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h73250 : p2476 ∨ p2470)
    (h43092 : (¬ p2230) ∨ (¬ p2476) ∨ (¬ p3083) ∨ (¬ p3238))
    : p2406 ∨ (¬ p3083) ∨ p2470 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2406) := (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43092 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step87478 (p2230 p2406 p2528 p2534 p2656 p3083 p3238 p4256 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h73542 : p4256 ∨ p3083)
    (h73268 : p2534 ∨ p2528)
    (h59514 : (¬ p2230) ∨ (¬ p2534) ∨ (¬ p2656) ∨ (¬ p3238) ∨ (¬ p4256))
    : (¬ p2230) ∨ (¬ p2656) ∨ p2406 ∨ p3083 ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h59514 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step87481 (p2230 p2274 p2406 p3238 p3389 p3540 p3921 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h73402 : p3540 ∨ p3389)
    (h42763 : (¬ p2230) ∨ (¬ p2274) ∨ (¬ p3238) ∨ (¬ p3540) ∨ (¬ p3921))
    : p2406 ∨ (¬ p2274) ∨ p3389 ∨ (¬ p2230) ∨ (¬ p3921) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2406) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42763 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step87489 (p2230 p2417 p3516 p3821 p4644 p5197 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h41074 : (¬ p2230) ∨ (¬ p2417) ∨ (¬ p3821) ∨ (¬ p4644) ∨ (¬ p5197))
    : (¬ p2417) ∨ (¬ p2230) ∨ (¬ p4644) ∨ p3516 ∨ (¬ p5197) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41074 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step87491 (p2230 p2352 p2383 p2387 p2577 p4715 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h63223 : (¬ p2230) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2577) ∨ (¬ p4715))
    : (¬ p2577) ∨ (¬ p2352) ∨ p2383 ∨ (¬ p4715) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2577 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h63223 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step87492 (p2230 p2307 p2313 p2553 p2577 p4715 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h49734 : (¬ p2230) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p4715))
    : (¬ p2553) ∨ (¬ p2230) ∨ (¬ p2577) ∨ (¬ p4715) ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49734 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step87494 (p2187 p2230 p2563 p2608 p2737 p2743 p3005 p3877 p3954 p4774 p5190 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73498 : p3954 ∨ p2608)
    (h73298 : p2743 ∨ p2737)
    (h58649 : (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p2743) ∨ (¬ p3877) ∨ (¬ p3954) ∨ (¬ p4774) ∨ (¬ p5190))
    : p3005 ∨ p2608 ∨ p2737 ∨ (¬ p4774) ∨ (¬ p2187) ∨ (¬ p2563) ∨ (¬ p5190) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h58649 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step87495 (p2230 p2577 p3564 p3654 p3946 p4715 : Prop)
    (h73492 : p3946 ∨ p3654)
    (h49947 : (¬ p2230) ∨ (¬ p2577) ∨ (¬ p3564) ∨ (¬ p3946) ∨ (¬ p4715))
    : (¬ p3564) ∨ p3654 ∨ (¬ p4715) ∨ (¬ p2577) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3654) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h49947 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step87496 (p2230 p2284 p2459 p3125 p3399 p3527 p3548 p3879 p4330 p4348 p4366 p5190 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73404 : p3548 ∨ p3527)
    (h73562 : p4348 ∨ p2459)
    (h42363 : (¬ p2230) ∨ (¬ p2284) ∨ (¬ p3125) ∨ (¬ p3548) ∨ (¬ p3879) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4366) ∨ (¬ p5190))
    : (¬ p3125) ∨ p3399 ∨ (¬ p2230) ∨ p3527 ∨ p2459 ∨ (¬ p3879) ∨ (¬ p4330) ∨ (¬ p2284) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42363 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step87497 (p2230 p2440 p3246 p3516 p3821 p5197 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h53726 : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p3246) ∨ (¬ p3821) ∨ (¬ p5197))
    : (¬ p3246) ∨ (¬ p2230) ∨ (¬ p2440) ∨ p3516 ∨ (¬ p5197) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53726 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step87499 (p2230 p2383 p2387 p2668 p2787 p2870 p3246 p3323 p3362 p3698 p4037 p4625 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73246 : p2387 ∨ p2383)
    (h56279 : (¬ p2230) ∨ (¬ p2387) ∨ (¬ p2668) ∨ (¬ p2787) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3362) ∨ (¬ p3698) ∨ (¬ p4037) ∨ (¬ p4625))
    : (¬ p2668) ∨ (¬ p3246) ∨ p3323 ∨ (¬ p2787) ∨ (¬ p2230) ∨ (¬ p4625) ∨ p2383 ∨ (¬ p3362) ∨ (¬ p3698) ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h56279 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step87500 (p2630 p2685 p2810 p3572 p4112 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73419 : (¬ p2685) ∨ (¬ p3572))
    (h30800 : (¬ p2810) ∨ p3572 ∨ (¬ p4112))
    : p2630 ∨ (¬ p4112) ∨ (¬ p2685) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p4112 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p3572) := (Or.elim h73419 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h30800 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step87501 (p2685 p3136 p3572 p4315 p4386 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73419 : (¬ p2685) ∨ (¬ p3572))
    (h24324 : p3572 ∨ (¬ p4315) ∨ (¬ p4386))
    : (¬ p4386) ∨ p3136 ∨ (¬ p2685) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4386 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3136) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : (¬ p3572) := (Or.elim h73419 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h24324 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u0)))))))

theorem step87503 (p2685 p3005 p3572 p3877 p4044 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73419 : (¬ p2685) ∨ (¬ p3572))
    (h6595 : p3572 ∨ (¬ p3877) ∨ (¬ p4044))
    : p3005 ∨ (¬ p4044) ∨ (¬ p2685) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p3572) := (Or.elim h73419 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h6595 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step87506 (p2177 p2264 p2299 p2737 p2743 p2753 p3425 p3471 p4325 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h73298 : p2743 ∨ p2737)
    (h73396 : p3471 ∨ p3425)
    (h56879 : (¬ p2264) ∨ (¬ p2299) ∨ (¬ p2743) ∨ (¬ p2753) ∨ (¬ p3471) ∨ (¬ p4325))
    : (¬ p2264) ∨ p2177 ∨ (¬ p2753) ∨ p2737 ∨ (¬ p4325) ∨ p3425 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2177) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h56879 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step87507 (p2630 p2707 p2737 p2743 p2810 p4325 p4652 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73316 : p2810 ∨ p2630)
    (h53293 : (¬ p2707) ∨ (¬ p2743) ∨ (¬ p2810) ∨ (¬ p4325) ∨ (¬ p4652))
    : (¬ p2707) ∨ p2737 ∨ p2630 ∨ (¬ p4652) ∨ (¬ p4325) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h53293 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step87509 (p2707 p2737 p2743 p2807 p3414 p4325 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73392 : p3414 ∨ p2807)
    (h71691 : (¬ p2707) ∨ (¬ p2743) ∨ (¬ p3414) ∨ (¬ p4325))
    : p2737 ∨ p2807 ∨ (¬ p4325) ∨ (¬ p2707) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2807) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71691 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step87517 (p2177 p2717 p3552 p3659 p4325 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h21085 : (¬ p2177) ∨ (¬ p3552) ∨ (¬ p3659) ∨ (¬ p4325))
    : (¬ p3552) ∨ p2717 ∨ (¬ p4325) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3552 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h21085 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step87518 (p2264 p2717 p3553 p3659 p4325 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h73409 : (¬ p2264) ∨ (¬ p3553))
    (h21084 : p3553 ∨ (¬ p3659) ∨ (¬ p4325))
    : p2717 ∨ (¬ p2264) ∨ (¬ p4325) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p3553) := (Or.elim h73409 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h21084 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step87528 (p2264 p2696 p2707 p2737 p2743 p4325 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h43484 : (¬ p2264) ∨ (¬ p2696) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p4325))
    : (¬ p2707) ∨ p2737 ∨ (¬ p2696) ∨ (¬ p2264) ∨ (¬ p4325) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43484 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step87530 (p2630 p2696 p2810 p3365 p3425 p3471 p4325 p4652 : Prop)
    (h73396 : p3471 ∨ p3425)
    (h73390 : p3365 ∨ p2696)
    (h73316 : p2810 ∨ p2630)
    (h41623 : (¬ p2810) ∨ (¬ p3365) ∨ (¬ p3471) ∨ (¬ p4325) ∨ (¬ p4652))
    : p3425 ∨ (¬ p4652) ∨ p2696 ∨ (¬ p4325) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3425) := (fun h => hn (Or.inl h));
    let u1 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41623 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1)))))))))))

end ElevenRUP
