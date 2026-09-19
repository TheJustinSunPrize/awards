import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step81177 (p2156 p2563 p2737 p3363 p3367 p3585 p3646 p3904 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73428 : p3585 ∨ p3367)
    (h46996 : (¬ p2563) ∨ (¬ p2737) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p3646) ∨ (¬ p3904))
    : (¬ p2737) ∨ p2156 ∨ (¬ p3904) ∨ (¬ p3363) ∨ (¬ p2563) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h46996 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step81182 (p2230 p2589 p2829 p3363 p3367 p3585 p4390 p4717 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h73284 : p2589 ∨ p2230)
    (h48320 : (¬ p2589) ∨ (¬ p2829) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p4390) ∨ (¬ p4717))
    : (¬ p2829) ∨ (¬ p4390) ∨ (¬ p3363) ∨ (¬ p4717) ∨ p3367 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h48320 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step81184 (p2417 p2761 p2850 p3363 p3389 p3540 p4278 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73546 : p4278 ∨ p2417)
    (h73402 : p3540 ∨ p3389)
    (h47399 : (¬ p2850) ∨ (¬ p3363) ∨ (¬ p3540) ∨ (¬ p4278) ∨ (¬ p4381))
    : p2761 ∨ p2417 ∨ (¬ p2850) ∨ (¬ p3363) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47399 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step81186 (p2230 p2589 p2707 p3363 p3367 p3585 p3658 p4646 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h73284 : p2589 ∨ p2230)
    (h41209 : (¬ p2589) ∨ (¬ p2707) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p3658) ∨ (¬ p4646))
    : (¬ p2707) ∨ (¬ p3658) ∨ p3367 ∨ (¬ p4646) ∨ p2230 ∨ (¬ p3363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3658 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41209 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step81189 (p2177 p2230 p2373 p2589 p2774 p3309 p3363 p3367 p3585 p3880 p3918 p4905 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h73490 : p3880 ∨ p2373)
    (h73428 : p3585 ∨ p3367)
    (h71493 : (¬ p3585) ∨ (¬ p3880) ∨ (¬ p2177) ∨ (¬ p2774) ∨ (¬ p2589) ∨ (¬ p3918) ∨ (¬ p4905) ∨ (¬ p3363) ∨ (¬ p3309))
    : (¬ p3309) ∨ (¬ p4905) ∨ p2230 ∨ (¬ p3918) ∨ (¬ p2177) ∨ p2373 ∨ (¬ p2774) ∨ (¬ p3363) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3918 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h71493 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step81190 (p2608 p2737 p2743 p3379 p3954 p4752 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73498 : p3954 ∨ p2608)
    (h71072 : (¬ p4752) ∨ (¬ p3379) ∨ (¬ p2743) ∨ (¬ p3954))
    : p2737 ∨ p2608 ∨ (¬ p4752) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71072 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step81192 (p2741 p2811 p2946 p2992 p3367 p3662 p4752 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h40948 : (¬ p2741) ∨ (¬ p2811) ∨ (¬ p2946) ∨ (¬ p3367) ∨ (¬ p3662) ∨ (¬ p4752))
    : p2992 ∨ (¬ p2741) ∨ (¬ p2946) ∨ (¬ p3367) ∨ (¬ p2811) ∨ (¬ p4752) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h40948 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step81194 (p2741 p2811 p3166 p3189 p3367 p4360 p4752 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h41556 : (¬ p2741) ∨ (¬ p2811) ∨ (¬ p3166) ∨ (¬ p3367) ∨ (¬ p4360) ∨ (¬ p4752))
    : (¬ p2811) ∨ (¬ p3166) ∨ (¬ p4752) ∨ (¬ p3367) ∨ p3189 ∨ (¬ p2741) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2811 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41556 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step81197 (p2696 p3201 p3362 p3365 p3389 p3876 p4752 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73390 : p3365 ∨ p2696)
    (h41092 : (¬ p3362) ∨ (¬ p3365) ∨ (¬ p3389) ∨ (¬ p3876) ∨ (¬ p4752))
    : p3201 ∨ p2696 ∨ (¬ p4752) ∨ (¬ p3362) ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41092 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step81200 (p2230 p2696 p2850 p3365 p3684 p4752 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73390 : p3365 ∨ p2696)
    (h66770 : (¬ p3684) ∨ (¬ p2230) ∨ (¬ p4752) ∨ (¬ p3365))
    : p2850 ∨ (¬ p2230) ∨ (¬ p4752) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h66770 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step81203 (p2518 p2737 p2743 p3541 p3641 p3874 p4752 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73484 : p3874 ∨ p3641)
    (h51945 : (¬ p2518) ∨ (¬ p2743) ∨ (¬ p3541) ∨ (¬ p3874) ∨ (¬ p4752))
    : (¬ p2518) ∨ p2737 ∨ p3641 ∨ (¬ p3541) ∨ (¬ p4752) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h51945 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step81206 (p2737 p2743 p2922 p3201 p3541 p3876 p4752 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73486 : p3876 ∨ p3201)
    (h52199 : (¬ p2743) ∨ (¬ p2922) ∨ (¬ p3541) ∨ (¬ p3876) ∨ (¬ p4752))
    : p2737 ∨ (¬ p3541) ∨ (¬ p2922) ∨ p3201 ∨ (¬ p4752) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h52199 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step81207 (p2493 p2737 p2743 p3422 p3541 p3584 p4752 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73426 : p3584 ∨ p3422)
    (h51940 : (¬ p2493) ∨ (¬ p2743) ∨ (¬ p3541) ∨ (¬ p3584) ∨ (¬ p4752))
    : p2737 ∨ (¬ p3541) ∨ p3422 ∨ (¬ p2493) ∨ (¬ p4752) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h51940 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step81211 (p2136 p2598 p2870 p3051 p3556 p4313 p4752 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h57106 : (¬ p2136) ∨ (¬ p2598) ∨ (¬ p2870) ∨ (¬ p3556) ∨ (¬ p4313) ∨ (¬ p4752))
    : (¬ p2870) ∨ p3051 ∨ (¬ p4752) ∨ (¬ p4313) ∨ (¬ p2598) ∨ (¬ p2136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h57106 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step81213 (p2737 p2743 p3193 p3222 p3541 p4752 p5160 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73298 : p2743 ∨ p2737)
    (h58782 : (¬ p2743) ∨ (¬ p3222) ∨ (¬ p3541) ∨ (¬ p4752) ∨ (¬ p5160))
    : p3193 ∨ (¬ p5160) ∨ (¬ p4752) ∨ (¬ p3541) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h58782 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step81219 (p2132 p2138 p2839 p3366 p3583 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73423 : (¬ p2839) ∨ (¬ p3583))
    (h26499 : (¬ p2138) ∨ (¬ p3366) ∨ p3583)
    : p2132 ∨ (¬ p2839) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p3583) := (Or.elim h73423 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h26499 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u4 r1)))))))

theorem step81221 (p2406 p2737 p2839 p3238 p3367 p3583 p3585 p4749 : Prop)
    (h73423 : (¬ p2839) ∨ (¬ p3583))
    (h73374 : p3238 ∨ p2406)
    (h73428 : p3585 ∨ p3367)
    (h66663 : (¬ p3585) ∨ p3583 ∨ (¬ p4749) ∨ (¬ p2737) ∨ (¬ p3238))
    : (¬ p2839) ∨ (¬ p2737) ∨ p2406 ∨ p3367 ∨ (¬ p4749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2839 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3583) := (Or.elim h73423 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h66663 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step81222 (p2839 p3367 p3583 p3585 p3641 p3874 p4608 : Prop)
    (h73423 : (¬ p2839) ∨ (¬ p3583))
    (h73484 : p3874 ∨ p3641)
    (h73428 : p3585 ∨ p3367)
    (h66687 : p3583 ∨ (¬ p4608) ∨ (¬ p3874) ∨ (¬ p3585))
    : (¬ p2839) ∨ p3641 ∨ p3367 ∨ (¬ p4608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2839 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3583) := (Or.elim h73423 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u5 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h66687 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step81223 (p2839 p3054 p3367 p3583 p3585 : Prop)
    (h73423 : (¬ p2839) ∨ (¬ p3583))
    (h73428 : p3585 ∨ p3367)
    (h37227 : (¬ p3054) ∨ p3583 ∨ (¬ p3585))
    : (¬ p2839) ∨ p3367 ∨ (¬ p3054) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2839 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3367) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3054 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3583) := (Or.elim h73423 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h37227 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step81224 (p2737 p2743 p2839 p3583 p4392 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73423 : (¬ p2839) ∨ (¬ p3583))
    (h28123 : (¬ p2743) ∨ p3583 ∨ (¬ p4392))
    : p2737 ∨ (¬ p2839) ∨ (¬ p4392) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p3583) := (Or.elim h73423 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h28123 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step81225 (p2737 p2743 p4842 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h46869 : (¬ p2743) ∨ p4842)
    : p2737 ∨ p4842 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4842) := (fun h => hn (Or.inr h));
    let u2 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h46869 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step81228 (p2274 p2284 p2737 p2743 p2946 p2952 p3097 p3361 p3952 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73330 : p2952 ∨ p2946)
    (h73298 : p2743 ∨ p2737)
    (h73352 : p3097 ∨ p2274)
    (h45300 : (¬ p2743) ∨ (¬ p2952) ∨ (¬ p3097) ∨ (¬ p3361) ∨ (¬ p3952))
    : p2284 ∨ p2946 ∨ (¬ p3361) ∨ p2737 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2284) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45300 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step81232 (p2284 p2696 p2737 p2743 p2829 p3589 p3952 p4185 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73496 : p3952 ∨ p2284)
    (h45230 : (¬ p2696) ∨ (¬ p2743) ∨ (¬ p2829) ∨ (¬ p3589) ∨ (¬ p3952) ∨ (¬ p4185))
    : p2737 ∨ (¬ p2829) ∨ (¬ p4185) ∨ p2284 ∨ (¬ p3589) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45230 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step81233 (p2177 p2295 p2299 p2331 p2737 p2743 p2963 p3361 p3568 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73416 : p3568 ∨ p2295)
    (h73234 : p2299 ∨ p2177)
    (h73298 : p2743 ∨ p2737)
    (h46814 : (¬ p2299) ∨ (¬ p2743) ∨ (¬ p2963) ∨ (¬ p3361) ∨ (¬ p3568))
    : p2331 ∨ p2295 ∨ (¬ p3361) ∨ p2177 ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46814 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step81237 (p2440 p2563 p2651 p2657 p2737 p2743 p3361 p4110 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73288 : p2657 ∨ p2651)
    (h73516 : p4110 ∨ p2563)
    (h43007 : (¬ p2440) ∨ (¬ p2657) ∨ (¬ p2743) ∨ (¬ p3361) ∨ (¬ p4110))
    : p2737 ∨ p2651 ∨ (¬ p2440) ∨ (¬ p3361) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43007 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step81238 (p2373 p2427 p2608 p2737 p2743 p3005 p3051 p3877 p3954 p4043 p4235 p4399 p5190 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73498 : p3954 ∨ p2608)
    (h73298 : p2743 ∨ p2737)
    (h73488 : p3877 ∨ p3005)
    (h62467 : (¬ p2373) ∨ (¬ p2743) ∨ (¬ p3051) ∨ (¬ p3877) ∨ (¬ p3954) ∨ (¬ p4043) ∨ (¬ p4235) ∨ (¬ p4399) ∨ (¬ p5190))
    : (¬ p3051) ∨ p2427 ∨ (¬ p4399) ∨ p2608 ∨ (¬ p5190) ∨ (¬ p2373) ∨ p2737 ∨ (¬ p4043) ∨ p3005 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h62467 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step81239 (p2737 p2743 p2901 p2946 p2952 p3246 p3361 p3690 p4320 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73552 : p4320 ∨ p2901)
    (h73298 : p2743 ∨ p2737)
    (h73446 : p3690 ∨ p3246)
    (h42781 : (¬ p2743) ∨ (¬ p2952) ∨ (¬ p3361) ∨ (¬ p3690) ∨ (¬ p4320))
    : p2946 ∨ p2901 ∨ (¬ p3361) ∨ p2737 ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42781 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step81242 (p2274 p2737 p2743 p2839 p2860 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h63651 : (¬ p2274) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p2860))
    : (¬ p2839) ∨ (¬ p2274) ∨ p2737 ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2839 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h63651 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step81245 (p2122 p2295 p2737 p2743 p2829 p3568 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73416 : p3568 ∨ p2295)
    (h47382 : (¬ p2122) ∨ (¬ p2743) ∨ (¬ p2829) ∨ (¬ p3568))
    : (¬ p2829) ∨ p2737 ∨ (¬ p2122) ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47382 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step81246 (p2122 p2696 p2737 p2743 p2829 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h43047 : (¬ p2122) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p2829))
    : (¬ p2829) ∨ p2737 ∨ (¬ p2122) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43047 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step81247 (p2737 p2743 p2829 p3483 p3564 p4137 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h73298 : p2743 ∨ p2737)
    (h52550 : (¬ p2743) ∨ (¬ p2829) ∨ (¬ p3483) ∨ (¬ p4137))
    : (¬ p3483) ∨ p3564 ∨ p2737 ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52550 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81251 (p2177 p2295 p2737 p2743 p2829 p4328 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h53012 : (¬ p2177) ∨ (¬ p2295) ∨ (¬ p2743) ∨ (¬ p2829) ∨ (¬ p4328))
    : p2737 ∨ (¬ p2829) ∨ (¬ p2177) ∨ (¬ p4328) ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h53012 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step81252 (p2373 p2619 p2737 p2743 p2839 p3880 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73298 : p2743 ∨ p2737)
    (h54880 : (¬ p2619) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p3880))
    : (¬ p2619) ∨ (¬ p2839) ∨ p2373 ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54880 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81256 (p2241 p2685 p2737 p2743 p2996 p3027 p3572 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73340 : p3027 ∨ p2996)
    (h73420 : p3572 ∨ p2685)
    (h59168 : (¬ p2241) ∨ (¬ p2743) ∨ (¬ p3027) ∨ (¬ p3572))
    : p2737 ∨ p2996 ∨ p2685 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h59168 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step81257 (p2608 p2737 p2743 p2992 p3136 p3954 p4315 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73498 : p3954 ∨ p2608)
    (h73550 : p4315 ∨ p3136)
    (h45072 : (¬ p2743) ∨ (¬ p2992) ∨ (¬ p3954) ∨ (¬ p4315))
    : (¬ p2992) ∨ p2737 ∨ p2608 ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45072 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step81258 (p2608 p2630 p2727 p2737 p2743 p2810 p3954 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73316 : p2810 ∨ p2630)
    (h73498 : p3954 ∨ p2608)
    (h47357 : (¬ p2727) ∨ (¬ p2743) ∨ (¬ p2810) ∨ (¬ p3954))
    : p2737 ∨ (¬ p2727) ∨ p2630 ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47357 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step81261 (p2143 p2737 p2743 p3319 p3654 p3946 p4198 p4869 p5052 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73492 : p3946 ∨ p3654)
    (h63726 : (¬ p2143) ∨ (¬ p2743) ∨ (¬ p3319) ∨ (¬ p3946) ∨ (¬ p4198) ∨ (¬ p4869) ∨ (¬ p5052))
    : (¬ p3319) ∨ (¬ p4869) ∨ p2737 ∨ (¬ p5052) ∨ p3654 ∨ (¬ p2143) ∨ (¬ p4198) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4869 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5052 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63726 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step81264 (p2696 p2737 p2743 p2753 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h3634 : (¬ p2696) ∨ (¬ p2743) ∨ (¬ p2753))
    : p2737 ∨ (¬ p2753) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h3634 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step81265 (p2177 p2295 p2737 p2743 p2753 p2774 p4328 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h53013 : (¬ p2177) ∨ (¬ p2295) ∨ (¬ p2743) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p4328))
    : p2737 ∨ (¬ p2753) ∨ (¬ p2177) ∨ (¬ p2774) ∨ (¬ p4328) ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h53013 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step81266 (p2608 p2737 p2743 p2751 p3954 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73498 : p3954 ∨ p2608)
    (h44946 : (¬ p2743) ∨ p2751 ∨ (¬ p3954))
    : p2751 ∨ p2737 ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2751) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44946 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step81268 (p2284 p2608 p2737 p2743 p3136 p3952 p3954 p4315 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73298 : p2743 ∨ p2737)
    (h73550 : p4315 ∨ p3136)
    (h73496 : p3952 ∨ p2284)
    (h46288 : (¬ p2743) ∨ (¬ p3952) ∨ (¬ p3954) ∨ (¬ p4315))
    : p2608 ∨ p2737 ∨ p3136 ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46288 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step81269 (p2608 p2630 p2737 p2743 p2810 p3016 p3574 p3954 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73298 : p2743 ∨ p2737)
    (h73422 : p3574 ∨ p3016)
    (h73316 : p2810 ∨ p2630)
    (h44155 : (¬ p2743) ∨ (¬ p2810) ∨ (¬ p3574) ∨ (¬ p3954))
    : p2608 ∨ p2737 ∨ p3016 ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44155 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81270 (p2177 p2553 p2573 p2608 p2737 p2743 p3005 p3877 p3954 p4041 p5190 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73298 : p2743 ∨ p2737)
    (h73498 : p3954 ∨ p2608)
    (h42089 : (¬ p2177) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2743) ∨ (¬ p3877) ∨ (¬ p3954) ∨ (¬ p4041) ∨ (¬ p5190))
    : p3005 ∨ (¬ p2553) ∨ p2737 ∨ (¬ p4041) ∨ (¬ p2573) ∨ (¬ p2177) ∨ (¬ p5190) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h42089 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step81272 (p2608 p2737 p2743 p3755 p3954 p4035 p5284 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73298 : p2743 ∨ p2737)
    (h73506 : p4035 ∨ p3755)
    (h62302 : (¬ p2743) ∨ (¬ p3954) ∨ (¬ p4035) ∨ (¬ p5284))
    : (¬ p5284) ∨ p2608 ∨ p2737 ∨ p3755 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62302 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step81273 (p2331 p2493 p2553 p2598 p2737 p2743 p2963 p3323 p3361 p3590 p4037 p4620 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73298 : p2743 ∨ p2737)
    (h73508 : p4037 ∨ p3323)
    (h71497 : (¬ p2493) ∨ (¬ p3590) ∨ (¬ p2598) ∨ (¬ p4037) ∨ (¬ p2553) ∨ (¬ p2743) ∨ (¬ p4620) ∨ (¬ p3361) ∨ (¬ p2963))
    : (¬ p2553) ∨ p2331 ∨ (¬ p4620) ∨ (¬ p3590) ∨ p2737 ∨ (¬ p2598) ∨ p3323 ∨ (¬ p3361) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h71497 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step81274 (p2737 p2743 p3364 p3367 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h18167 : (¬ p2743) ∨ (¬ p3364) ∨ (¬ p3367))
    : p2737 ∨ (¬ p3367) ∨ (¬ p3364) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h18167 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u1)))))))

theorem step81280 (p2230 p2406 p2589 p2737 p2743 p3363 p3541 p4752 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73284 : p2589 ∨ p2230)
    (h41290 : (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2743) ∨ (¬ p3363) ∨ (¬ p3541) ∨ (¬ p4752))
    : p2737 ∨ (¬ p3541) ∨ (¬ p3363) ∨ p2230 ∨ (¬ p4752) ∨ (¬ p2406) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41290 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step81281 (p2737 p2743 p2774 p2780 p2829 p3362 p3363 p4752 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73308 : p2780 ∨ p2774)
    (h51941 : (¬ p2743) ∨ (¬ p2780) ∨ (¬ p2829) ∨ (¬ p3362) ∨ (¬ p3363) ∨ (¬ p4752))
    : (¬ p2829) ∨ p2737 ∨ (¬ p4752) ∨ p2774 ∨ (¬ p3362) ∨ (¬ p3363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h51941 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step81283 (p2598 p2737 p2743 p2753 p3364 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h20358 : (¬ p2598) ∨ (¬ p2743) ∨ (¬ p2753) ∨ (¬ p3364))
    : p2737 ∨ (¬ p2753) ∨ (¬ p2598) ∨ (¬ p3364) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h20358 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step81285 (p2737 p2743 p3434 p3631 p3687 p4324 p4782 : Prop)
    (h73556 : p4324 ∨ p3434)
    (h73298 : p2743 ∨ p2737)
    (h41191 : (¬ p2743) ∨ (¬ p3631) ∨ (¬ p3687) ∨ (¬ p4324) ∨ (¬ p4782))
    : (¬ p3687) ∨ (¬ p3631) ∨ (¬ p4782) ∨ p3434 ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3687 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4782 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41191 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step81290 (p2737 p2743 p2829 p4841 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h20280 : (¬ p2743) ∨ (¬ p2829) ∨ (¬ p4841))
    : (¬ p2829) ∨ (¬ p4841) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4841 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20280 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step81292 (p2737 p2743 p2829 p3005 p3256 p3877 p4118 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73488 : p3877 ∨ p3005)
    (h73520 : p4118 ∨ p3256)
    (h47165 : (¬ p2743) ∨ (¬ p2829) ∨ (¬ p3877) ∨ (¬ p4118))
    : (¬ p2829) ∨ p2737 ∨ p3005 ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47165 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step81293 (p2177 p2307 p2737 p2743 p2779 p2829 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h45759 : (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2743) ∨ (¬ p2779) ∨ (¬ p2829))
    : (¬ p2779) ∨ (¬ p2829) ∨ (¬ p2177) ∨ (¬ p2307) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2779 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45759 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step81298 (p2696 p2737 p2743 p3537 p3609 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h42976 : (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3537) ∨ (¬ p3609))
    : (¬ p3537) ∨ (¬ p3609) ∨ (¬ p2696) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3537 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42976 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step81299 (p2563 p2630 p2737 p2743 p2810 p2839 p3695 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73316 : p2810 ∨ p2630)
    (h44940 : (¬ p2563) ∨ (¬ p2743) ∨ (¬ p2810) ∨ (¬ p2839) ∨ (¬ p3695))
    : (¬ p2839) ∨ (¬ p3695) ∨ p2737 ∨ (¬ p2563) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2839 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h44940 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step81300 (p2132 p2138 p2630 p2737 p2743 p2810 p2839 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73298 : p2743 ∨ p2737)
    (h73316 : p2810 ∨ p2630)
    (h55155 : (¬ p2138) ∨ (¬ p2743) ∨ (¬ p2810) ∨ (¬ p2839))
    : (¬ p2839) ∨ p2132 ∨ p2737 ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2839 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55155 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step81302 (p2132 p2138 p2737 p2743 p2839 p3425 p3471 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73396 : p3471 ∨ p3425)
    (h73298 : p2743 ∨ p2737)
    (h44102 : (¬ p2138) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p3471))
    : p2132 ∨ (¬ p2839) ∨ p3425 ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44102 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step81303 (p2696 p2707 p2737 p2743 p3434 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h45706 : (¬ p2696) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p3434))
    : (¬ p2707) ∨ p2737 ∨ (¬ p3434) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45706 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step81305 (p2707 p2737 p2743 p4357 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h33855 : (¬ p2707) ∨ (¬ p2743) ∨ (¬ p4357))
    : p2737 ∨ (¬ p2707) ∨ (¬ p4357) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4357 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h33855 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step81306 (p2088 p2459 p2707 p2737 p2743 p3577 p4348 p4590 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73562 : p4348 ∨ p2459)
    (h48586 : (¬ p2088) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p3577) ∨ (¬ p4348) ∨ (¬ p4590))
    : (¬ p3577) ∨ (¬ p4590) ∨ (¬ p2707) ∨ p2737 ∨ p2459 ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3577 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48586 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step81307 (p2707 p2737 p2743 p2761 p3670 p4381 p5234 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73574 : p4381 ∨ p2761)
    (h56337 : (¬ p2707) ∨ (¬ p2743) ∨ (¬ p3670) ∨ (¬ p4381) ∨ (¬ p5234))
    : (¬ p2707) ∨ p2737 ∨ (¬ p5234) ∨ p2761 ∨ (¬ p3670) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5234 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56337 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step81310 (p2737 p2743 p3005 p3367 p3683 p3877 p5008 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73488 : p3877 ∨ p3005)
    (h54237 : (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3683) ∨ (¬ p3877) ∨ (¬ p5008))
    : p2737 ∨ p3005 ∨ (¬ p5008) ∨ (¬ p3367) ∨ (¬ p3683) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5008 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h54237 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step81311 (p2737 p2743 p3136 p3367 p3683 p4315 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73550 : p4315 ∨ p3136)
    (h69618 : (¬ p3367) ∨ (¬ p4315) ∨ (¬ p2743) ∨ (¬ p3683))
    : p2737 ∨ (¬ p3367) ∨ (¬ p3683) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69618 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step81312 (p2737 p2743 p2797 p3367 p3683 p4195 p4972 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73532 : p4195 ∨ p2797)
    (h40950 : (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3683) ∨ (¬ p4195) ∨ (¬ p4972))
    : p2737 ∨ p2797 ∨ (¬ p3683) ∨ (¬ p3367) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h40950 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step81314 (p2132 p2138 p2774 p2780 p3985 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73213 : (¬ p2132) ∨ (¬ p2138))
    (h29438 : p2138 ∨ (¬ p2780) ∨ (¬ p3985))
    : p2774 ∨ (¬ p2132) ∨ (¬ p3985) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3985 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p2138) := (Or.elim h73213 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h29438 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step81316 (p2132 p2138 p2230 p2589 p3695 p3905 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h73213 : (¬ p2132) ∨ (¬ p2138))
    (h34414 : p2138 ∨ (¬ p2589) ∨ (¬ p3695) ∨ (¬ p3905))
    : (¬ p3695) ∨ (¬ p3905) ∨ p2230 ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3695 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : (¬ p2138) := (Or.elim h73213 (fun q0 => (False.elim (q0 u3))) (fun r0 => r0));
    (Or.elim h34414 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step81317 (p2850 p3695 p4883 : Prop)
    (h73808 : p4883 ∨ (¬ p2850))
    (h8038 : p3695 ∨ (¬ p4883))
    : p3695 ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3695) := (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4883 := (Or.elim h73808 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h8038 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step81319 (p2850 p4883 p4884 : Prop)
    (h73808 : p4883 ∨ (¬ p2850))
    (h8041 : (¬ p4883) ∨ p4884)
    : (¬ p2850) ∨ p4884 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4884) := (fun h => hn (Or.inr h));
    let u2 : p4883 := (Or.elim h73808 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h8041 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step81320 (p2850 p4883 p4885 : Prop)
    (h73808 : p4883 ∨ (¬ p2850))
    (h8042 : (¬ p4883) ∨ p4885)
    : (¬ p2850) ∨ p4885 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4885) := (fun h => hn (Or.inr h));
    let u2 : p4883 := (Or.elim h73808 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h8042 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step81324 (p2307 p2497 p2850 p3309 p3549 p3567 p4030 p4389 p4715 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h61831 : (¬ p2307) ∨ (¬ p2497) ∨ (¬ p2850) ∨ (¬ p3549) ∨ (¬ p3567) ∨ (¬ p4030) ∨ (¬ p4389) ∨ (¬ p4715))
    : (¬ p2307) ∨ p3309 ∨ (¬ p4715) ∨ (¬ p4030) ∨ (¬ p2850) ∨ (¬ p4389) ∨ (¬ p2497) ∨ (¬ p3567) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3309) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h61831 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step81327 (p2493 p2499 p2573 p2696 p3362 p3365 p4030 p4752 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h73260 : p2499 ∨ p2493)
    (h55941 : (¬ p2499) ∨ (¬ p2573) ∨ (¬ p3362) ∨ (¬ p3365) ∨ (¬ p4030) ∨ (¬ p4752))
    : (¬ p2573) ∨ (¬ p4030) ∨ p2696 ∨ p2493 ∨ (¬ p4752) ∨ (¬ p3362) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55941 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step81337 (p2156 p2177 p2274 p2299 p2608 p3097 p3379 p3641 p3645 p3646 p3954 p4030 p4420 p4877 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73352 : p3097 ∨ p2274)
    (h73436 : p3646 ∨ p2156)
    (h73234 : p2299 ∨ p2177)
    (h54595 : (¬ p2299) ∨ (¬ p3097) ∨ (¬ p3379) ∨ (¬ p3641) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3954) ∨ (¬ p4030) ∨ (¬ p4420) ∨ (¬ p4877))
    : p2608 ∨ p2274 ∨ (¬ p3645) ∨ p2156 ∨ (¬ p3641) ∨ (¬ p3379) ∨ (¬ p4420) ∨ p2177 ∨ (¬ p4030) ∨ (¬ p4877) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h54595 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step81339 (p2156 p2187 p2363 p2608 p3333 p3379 p3645 p3646 p3954 p3989 p4030 p4332 p4347 p4877 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73436 : p3646 ∨ p2156)
    (h73498 : p3954 ∨ p2608)
    (h73502 : p3989 ∨ p2187)
    (h63062 : (¬ p3333) ∨ (¬ p3379) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3954) ∨ (¬ p3989) ∨ (¬ p4030) ∨ (¬ p4332) ∨ (¬ p4347) ∨ (¬ p4877))
    : (¬ p4030) ∨ p2363 ∨ p2156 ∨ p2608 ∨ (¬ p3645) ∨ (¬ p3333) ∨ (¬ p4332) ∨ (¬ p4877) ∨ (¬ p3379) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4030 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h63062 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step81344 (p2493 p2499 p2518 p3573 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h22597 : (¬ p2499) ∨ (¬ p2518) ∨ (¬ p3573))
    : (¬ p2518) ∨ p2493 ∨ (¬ p3573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2493) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h22597 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u2)))))))

theorem step81347 (p2493 p2499 p2518 p2553 p2588 p3083 p4256 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73282 : p2588 ∨ p2553)
    (h73542 : p4256 ∨ p3083)
    (h45521 : (¬ p2499) ∨ (¬ p2518) ∨ (¬ p2588) ∨ (¬ p4256))
    : (¬ p2518) ∨ p2493 ∨ p2553 ∨ p3083 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2493) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45521 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step81352 (p2493 p2499 p2518 p2553 p2588 p4157 p4405 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73282 : p2588 ∨ p2553)
    (h56322 : (¬ p2499) ∨ (¬ p2518) ∨ (¬ p2588) ∨ (¬ p4157) ∨ (¬ p4405))
    : (¬ p2518) ∨ (¬ p4157) ∨ p2493 ∨ p2553 ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56322 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step81357 (p2383 p2387 p2493 p2499 p2518 p2581 p4157 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h73260 : p2499 ∨ p2493)
    (h48607 : (¬ p2387) ∨ (¬ p2499) ∨ (¬ p2518) ∨ (¬ p2581) ∨ (¬ p4157))
    : (¬ p2518) ∨ p2383 ∨ (¬ p4157) ∨ (¬ p2581) ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2383) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48607 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step81360 (p2470 p2476 p2518 p3347 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h5857 : (¬ p2476) ∨ (¬ p2518) ∨ (¬ p3347))
    : (¬ p2518) ∨ p2470 ∨ (¬ p3347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2470) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h5857 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u2)))))))

theorem step81362 (p2230 p2406 p2518 p2531 p2668 p2696 p2797 p3238 p3324 p3365 p4079 p4195 p4433 p4736 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73386 : p3324 ∨ p2668)
    (h73374 : p3238 ∨ p2406)
    (h73390 : p3365 ∨ p2696)
    (h58468 : (¬ p2230) ∨ (¬ p2518) ∨ (¬ p2531) ∨ (¬ p3238) ∨ (¬ p3324) ∨ (¬ p3365) ∨ (¬ p4079) ∨ (¬ p4195) ∨ (¬ p4433) ∨ (¬ p4736))
    : p2797 ∨ (¬ p2518) ∨ (¬ p4433) ∨ p2668 ∨ (¬ p4736) ∨ p2406 ∨ (¬ p2230) ∨ (¬ p4079) ∨ (¬ p2531) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2531 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h58468 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step81364 (p2210 p2518 p2528 p3379 p3555 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h47146 : (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3379) ∨ (¬ p3555))
    : p2210 ∨ (¬ p2518) ∨ (¬ p3379) ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h47146 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81365 (p2241 p2247 p2518 p2528 p3379 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h47332 : (¬ p2247) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3379))
    : (¬ p2518) ∨ (¬ p2528) ∨ p2241 ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47332 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step81366 (p2156 p2177 p2245 p2274 p2406 p2518 p2651 p2657 p3083 p3238 p4256 p4521 : Prop)
    (h73542 : p4256 ∨ p3083)
    (h73288 : p2657 ∨ p2651)
    (h73374 : p3238 ∨ p2406)
    (h62591 : (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2245) ∨ (¬ p2274) ∨ (¬ p2518) ∨ (¬ p2657) ∨ (¬ p3238) ∨ (¬ p4256) ∨ (¬ p4521))
    : (¬ p2518) ∨ (¬ p2245) ∨ (¬ p2177) ∨ p3083 ∨ (¬ p2274) ∨ p2651 ∨ p2406 ∨ (¬ p2156) ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h62591 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step81367 (p2241 p2470 p2476 p2518 p2750 p3541 p4108 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h65253 : (¬ p2241) ∨ (¬ p2476) ∨ (¬ p2518) ∨ (¬ p2750) ∨ (¬ p3541) ∨ (¬ p4108))
    : (¬ p2518) ∨ p2470 ∨ (¬ p2750) ∨ (¬ p3541) ∨ (¬ p4108) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2470) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h65253 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step81372 (p2518 p2651 p2657 p2922 p2928 p3083 p4256 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73288 : p2657 ∨ p2651)
    (h73542 : p4256 ∨ p3083)
    (h61998 : (¬ p2518) ∨ (¬ p2657) ∨ (¬ p2928) ∨ (¬ p4256))
    : (¬ p2518) ∨ p2922 ∨ p2651 ∨ p3083 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2922) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61998 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step81377 (p2254 p2295 p2331 p2396 p2518 p2528 p2963 p3379 p3568 p4107 p4669 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73514 : p4107 ∨ p2396)
    (h73416 : p3568 ∨ p2295)
    (h51883 : (¬ p2254) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2963) ∨ (¬ p3379) ∨ (¬ p3568) ∨ (¬ p4107) ∨ (¬ p4669))
    : (¬ p2518) ∨ p2331 ∨ p2396 ∨ (¬ p2528) ∨ (¬ p3379) ∨ p2295 ∨ (¬ p2254) ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h51883 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step81379 (p2470 p2476 p2518 p2553 p2573 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h42653 : (¬ p2476) ∨ (¬ p2518) ∨ (¬ p2553) ∨ (¬ p2573))
    : (¬ p2518) ∨ (¬ p2553) ∨ p2470 ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42653 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step81381 (p2518 p2573 p2579 p3347 p3573 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h24509 : (¬ p2518) ∨ (¬ p2579) ∨ (¬ p3347) ∨ (¬ p3573))
    : (¬ p2518) ∨ p2573 ∨ (¬ p3573) ∨ (¬ p3347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h24509 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step81384 (p2470 p2476 p2518 p2608 p4108 p4376 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h54442 : (¬ p2476) ∨ (¬ p2518) ∨ (¬ p2608) ∨ (¬ p4108) ∨ (¬ p4376))
    : (¬ p2518) ∨ p2470 ∨ (¬ p2608) ∨ (¬ p4108) ∨ (¬ p4376) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2470) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h54442 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step81385 (p2470 p2476 p2493 p2499 p2518 p2553 p2588 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73250 : p2476 ∨ p2470)
    (h73282 : p2588 ∨ p2553)
    (h45528 : (¬ p2476) ∨ (¬ p2499) ∨ (¬ p2518) ∨ (¬ p2588))
    : (¬ p2518) ∨ p2493 ∨ p2470 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2493) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45528 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step81389 (p2406 p2470 p2476 p2518 p2630 p2662 p2810 p3238 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h73374 : p3238 ∨ p2406)
    (h73316 : p2810 ∨ p2630)
    (h44682 : (¬ p2476) ∨ (¬ p2518) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3238))
    : (¬ p2518) ∨ p2470 ∨ p2406 ∨ p2630 ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2470) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44682 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step81390 (p2406 p2518 p2528 p3238 p3256 p4118 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h73520 : p4118 ∨ p3256)
    (h57200 : (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3238) ∨ (¬ p4118))
    : (¬ p2518) ∨ (¬ p2528) ∨ p2406 ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h57200 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step81392 (p2518 p2881 p2922 p2928 p3570 p4404 p4647 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73418 : p3570 ∨ p2881)
    (h41045 : (¬ p2518) ∨ (¬ p2928) ∨ (¬ p3570) ∨ (¬ p4404) ∨ (¬ p4647))
    : p2922 ∨ (¬ p2518) ∨ (¬ p4404) ∨ (¬ p4647) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4404 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41045 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step81393 (p2264 p2449 p2518 p2528 p3051 p3246 p3379 p3553 p3556 p3690 p4524 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73410 : p3553 ∨ p2264)
    (h72962 : p4524)
    (h73414 : p3556 ∨ p3051)
    (h51882 : (¬ p2449) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3379) ∨ (¬ p3553) ∨ (¬ p3556) ∨ (¬ p3690) ∨ (¬ p4524))
    : (¬ p2449) ∨ (¬ p2528) ∨ (¬ p3379) ∨ p3246 ∨ p2264 ∨ (¬ p2518) ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p4524 := h72962;
    let u10 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h51882 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u9)))))))))))))))))

theorem step81394 (p2295 p2307 p2313 p2518 p2528 p3323 p3379 p4037 p4604 p5021 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73508 : p4037 ∨ p3323)
    (h63342 : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3379) ∨ (¬ p4037) ∨ (¬ p4604) ∨ (¬ p5021))
    : (¬ p2518) ∨ (¬ p2295) ∨ (¬ p5021) ∨ (¬ p3379) ∨ p2307 ∨ p3323 ∨ (¬ p4604) ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h63342 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step81396 (p2437 p2440 p2518 p3347 p3389 p3540 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h53264 : (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2518) ∨ (¬ p3347) ∨ (¬ p3540))
    : (¬ p2518) ∨ (¬ p3347) ∨ p3389 ∨ (¬ p2437) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h53264 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step81401 (p2122 p2396 p2518 p2528 p2774 p2780 p3379 p3822 p4107 p4669 p4736 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73472 : p3822 ∨ p2122)
    (h73308 : p2780 ∨ p2774)
    (h49629 : (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2780) ∨ (¬ p3379) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4669) ∨ (¬ p4736))
    : (¬ p2518) ∨ (¬ p2528) ∨ p2396 ∨ p2122 ∨ (¬ p4736) ∨ p2774 ∨ (¬ p3379) ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h49629 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step81405 (p2417 p2518 p2922 p2928 p4278 p4404 p4666 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73546 : p4278 ∨ p2417)
    (h41128 : (¬ p2518) ∨ (¬ p2928) ∨ (¬ p4278) ∨ (¬ p4404) ∨ (¬ p4666))
    : p2922 ∨ (¬ p2518) ∨ (¬ p4666) ∨ p2417 ∨ (¬ p4404) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4404 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41128 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step81406 (p2518 p2528 p2901 p3156 p3246 p3379 p3497 p3516 p3821 p5210 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h73470 : p3821 ∨ p3516)
    (h58170 : (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2901) ∨ (¬ p3246) ∨ (¬ p3379) ∨ (¬ p3497) ∨ (¬ p3821) ∨ (¬ p5210))
    : (¬ p2901) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3379) ∨ (¬ p3246) ∨ (¬ p5210) ∨ p3156 ∨ p3516 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u9 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h58170 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step81407 (p2254 p2518 p2528 p3286 p3292 p3379 p3461 p4604 p5284 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h58492 : (¬ p2254) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3292) ∨ (¬ p3379) ∨ (¬ p3461) ∨ (¬ p4604) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p2518) ∨ (¬ p2254) ∨ (¬ p3461) ∨ p3286 ∨ (¬ p3379) ∨ (¬ p2528) ∨ (¬ p4604) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h58492 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step81408 (p2254 p2518 p2528 p2901 p2946 p2952 p3246 p3379 p3690 p4320 p4669 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73446 : p3690 ∨ p3246)
    (h73552 : p4320 ∨ p2901)
    (h52078 : (¬ p2254) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2952) ∨ (¬ p3379) ∨ (¬ p3690) ∨ (¬ p4320) ∨ (¬ p4669))
    : (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2254) ∨ (¬ p3379) ∨ p2946 ∨ p3246 ∨ p2901 ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h52078 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step81410 (p2254 p2331 p2518 p2963 p3323 p3379 p3461 p4037 p4149 p4191 p5119 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73530 : p4191 ∨ p3461)
    (h73338 : p2963 ∨ p2331)
    (h63349 : (¬ p2254) ∨ (¬ p2518) ∨ (¬ p2963) ∨ (¬ p3379) ∨ (¬ p4037) ∨ (¬ p4149) ∨ (¬ p4191) ∨ (¬ p5119))
    : (¬ p4149) ∨ (¬ p2518) ∨ p3323 ∨ (¬ p5119) ∨ p3461 ∨ p2331 ∨ (¬ p2254) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4149 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h63349 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step81418 (p2245 p2518 p2651 p2657 p3083 p3201 p3590 p3876 p4256 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73288 : p2657 ∨ p2651)
    (h73542 : p4256 ∨ p3083)
    (h47797 : (¬ p2245) ∨ (¬ p2518) ∨ (¬ p2657) ∨ (¬ p3590) ∨ (¬ p3876) ∨ (¬ p4256))
    : (¬ p2518) ∨ p3201 ∨ (¬ p3590) ∨ p2651 ∨ p3083 ∨ (¬ p2245) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47797 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u8)))))))))))))

theorem step81419 (p2230 p2470 p2476 p2518 p2563 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h46171 : (¬ p2230) ∨ (¬ p2476) ∨ (¬ p2518) ∨ (¬ p2563))
    : (¬ p2518) ∨ p2470 ∨ (¬ p2230) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2470) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46171 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step81420 (p2252 p2363 p2518 p2608 p2750 p3166 p3172 p3256 p3379 p3954 p4118 p4596 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h73356 : p3172 ∨ p3166)
    (h73498 : p3954 ∨ p2608)
    (h62839 : (¬ p2252) ∨ (¬ p2363) ∨ (¬ p2518) ∨ (¬ p2750) ∨ (¬ p3172) ∨ (¬ p3379) ∨ (¬ p3954) ∨ (¬ p4118) ∨ (¬ p4596))
    : p3256 ∨ p3166 ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p4596) ∨ (¬ p2518) ∨ (¬ p3379) ∨ (¬ p2363) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h62839 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step81422 (p2518 p3193 p3222 p3358 : Prop)
    (h73363 : (¬ p3193) ∨ (¬ p3222))
    (h18539 : (¬ p2518) ∨ p3222 ∨ (¬ p3358))
    : (¬ p3193) ∨ (¬ p2518) ∨ (¬ p3358) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3193 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3222) := (Or.elim h73363 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    (Or.elim h18539 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step81424 (p2241 p2247 p2440 p2459 p2518 p2528 p2641 p2668 p3324 p4116 p4154 p4348 p4503 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73386 : p3324 ∨ p2668)
    (h73526 : p4154 ∨ p2641)
    (h73562 : p4348 ∨ p2459)
    (h54094 : (¬ p2247) ∨ (¬ p2440) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3324) ∨ (¬ p4116) ∨ (¬ p4154) ∨ (¬ p4348) ∨ (¬ p4503))
    : (¬ p4116) ∨ p2241 ∨ p2668 ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2440) ∨ p2641 ∨ (¬ p4503) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4116 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h54094 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step81425 (p2518 p2528 p2922 p2928 p3389 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h46531 : (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2928) ∨ (¬ p3389))
    : (¬ p2518) ∨ (¬ p2528) ∨ p2922 ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46531 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step81426 (p2230 p2406 p2518 p2531 p3146 p3238 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h42776 : (¬ p2230) ∨ (¬ p2518) ∨ (¬ p2531) ∨ (¬ p3146) ∨ (¬ p3238))
    : (¬ p2518) ∨ (¬ p3146) ∨ (¬ p2230) ∨ p2406 ∨ (¬ p2531) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2531 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42776 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step81428 (p2406 p2470 p2476 p2518 p2563 p3238 p4108 p4110 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h73516 : p4110 ∨ p2563)
    (h73374 : p3238 ∨ p2406)
    (h43964 : (¬ p2476) ∨ (¬ p2518) ∨ (¬ p3238) ∨ (¬ p4108) ∨ (¬ p4110))
    : (¬ p2518) ∨ p2470 ∨ p2563 ∨ (¬ p4108) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2470) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43964 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step81432 (p2177 p2299 p2518 p2922 p2928 p4404 p4712 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73234 : p2299 ∨ p2177)
    (h49265 : (¬ p2299) ∨ (¬ p2518) ∨ (¬ p2928) ∨ (¬ p4404) ∨ (¬ p4712))
    : p2922 ∨ (¬ p2518) ∨ p2177 ∨ (¬ p4404) ∨ (¬ p4712) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4404 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h49265 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step81437 (p2518 p2528 p3146 p3379 p3692 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h46945 : (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3379) ∨ (¬ p3692))
    : (¬ p2518) ∨ (¬ p2528) ∨ p3146 ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46945 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81439 (p2187 p2475 p2518 p3016 p3574 p3989 p4113 p4116 p4718 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h73422 : p3574 ∨ p3016)
    (h41986 : (¬ p2475) ∨ (¬ p2518) ∨ (¬ p3574) ∨ (¬ p3989) ∨ (¬ p4113) ∨ (¬ p4116) ∨ (¬ p4718))
    : (¬ p4113) ∨ (¬ p2518) ∨ (¬ p4718) ∨ (¬ p2475) ∨ p2187 ∨ p3016 ∨ (¬ p4116) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4113 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u8 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41986 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step81441 (p2437 p2459 p2518 p2922 p2928 p4404 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h56386 : (¬ p2437) ∨ (¬ p2459) ∨ (¬ p2518) ∨ (¬ p2928) ∨ (¬ p4404))
    : p2922 ∨ (¬ p2518) ∨ (¬ p4404) ∨ (¬ p2459) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4404 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h56386 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step81442 (p2210 p2518 p3379 p3555 p4034 p4610 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h42551 : (¬ p2518) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4034) ∨ (¬ p4610))
    : p2210 ∨ (¬ p2518) ∨ (¬ p4034) ∨ (¬ p4610) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4034 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4610 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42551 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step81444 (p2459 p2493 p2499 p2518 p2528 p4348 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73562 : p4348 ∨ p2459)
    (h43930 : (¬ p2499) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p4348))
    : (¬ p2518) ∨ p2493 ∨ (¬ p2528) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2493) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43930 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step81445 (p2459 p2518 p2528 p3379 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h42853 : (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3379) ∨ (¬ p4348))
    : (¬ p2518) ∨ (¬ p2528) ∨ p2459 ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42853 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81446 (p2254 p2284 p2518 p2528 p2946 p2952 p3125 p3379 p3744 p3952 p4604 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73454 : p3744 ∨ p3125)
    (h73496 : p3952 ∨ p2284)
    (h55089 : (¬ p2254) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2952) ∨ (¬ p3379) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p4604))
    : (¬ p2518) ∨ p2946 ∨ p3125 ∨ (¬ p3379) ∨ (¬ p4604) ∨ p2284 ∨ (¬ p2528) ∨ (¬ p2254) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h55089 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step81448 (p2156 p2254 p2264 p2284 p2518 p2528 p2881 p2950 p3379 p3553 p3646 p4386 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73410 : p3553 ∨ p2264)
    (h62376 : (¬ p2254) ∨ (¬ p2284) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2881) ∨ (¬ p2950) ∨ (¬ p3379) ∨ (¬ p3553) ∨ (¬ p3646) ∨ (¬ p4386))
    : (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2950) ∨ (¬ p2284) ∨ p2156 ∨ p2264 ∨ (¬ p4386) ∨ (¬ p3379) ∨ (¬ p2254) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h62376 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step81451 (p2518 p3083 p3193 p3276 p4256 p4425 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73542 : p4256 ∨ p3083)
    (h55658 : (¬ p2518) ∨ (¬ p3193) ∨ (¬ p4256) ∨ (¬ p4425))
    : (¬ p3193) ∨ p3276 ∨ p3083 ∨ (¬ p2518) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3193 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h55658 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81453 (p2363 p2518 p2528 p3379 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h42875 : (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3379) ∨ (¬ p4347))
    : (¬ p2518) ∨ (¬ p2528) ∨ p2363 ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42875 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81456 (p2274 p2331 p2518 p2528 p2963 p3097 p3125 p3323 p3379 p4037 p4236 p4736 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73508 : p4037 ∨ p3323)
    (h73352 : p3097 ∨ p2274)
    (h55699 : (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2963) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3379) ∨ (¬ p4037) ∨ (¬ p4236) ∨ (¬ p4736))
    : (¬ p3125) ∨ (¬ p2518) ∨ p2331 ∨ (¬ p4736) ∨ (¬ p3379) ∨ (¬ p4236) ∨ (¬ p2528) ∨ p3323 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u11 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h55699 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step81467 (p2518 p3016 p3083 p3564 p4256 : Prop)
    (h73542 : p4256 ∨ p3083)
    (h57788 : (¬ p2518) ∨ (¬ p3016) ∨ (¬ p3564) ∨ (¬ p4256))
    : (¬ p2518) ∨ (¬ p3564) ∨ (¬ p3016) ∨ p3083 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h57788 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81471 (p2493 p2499 p2518 p2528 p2573 p4079 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h50320 : (¬ p2499) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2573) ∨ (¬ p4079))
    : (¬ p2518) ∨ p2493 ∨ (¬ p4079) ∨ (¬ p2573) ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2493) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h50320 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step81476 (p2192 p2518 p2563 p4173 p4202 p4610 : Prop)
    (h73528 : p4173 ∨ p2192)
    (h41927 : (¬ p2518) ∨ (¬ p2563) ∨ (¬ p4173) ∨ (¬ p4202) ∨ (¬ p4610))
    : p2192 ∨ (¬ p2518) ∨ (¬ p4610) ∨ (¬ p4202) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2192) := (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4610 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41927 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step81478 (p2220 p2406 p2518 p2531 p3238 p4120 p4533 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h73374 : p3238 ∨ p2406)
    (h60960 : (¬ p2518) ∨ (¬ p2531) ∨ (¬ p3238) ∨ (¬ p4120) ∨ (¬ p4533))
    : (¬ p2518) ∨ p2220 ∨ (¬ p2531) ∨ p2406 ∨ (¬ p4533) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2531 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60960 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step81480 (p2252 p2295 p2307 p2313 p2518 p2608 p2668 p2750 p3324 p3379 p3954 p3983 p4596 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73238 : p2313 ∨ p2307)
    (h73386 : p3324 ∨ p2668)
    (h58090 : (¬ p2252) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2518) ∨ (¬ p2750) ∨ (¬ p3324) ∨ (¬ p3379) ∨ (¬ p3954) ∨ (¬ p3983) ∨ (¬ p4596))
    : (¬ p2518) ∨ p2608 ∨ (¬ p4596) ∨ (¬ p2252) ∨ (¬ p3379) ∨ (¬ p2295) ∨ (¬ p3983) ∨ p2307 ∨ p2668 ∨ (¬ p2750) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3983 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h58090 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step81482 (p2088 p2475 p2518 p3256 p3878 p4118 p4814 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h41511 : (¬ p2088) ∨ (¬ p2475) ∨ (¬ p2518) ∨ (¬ p3878) ∨ (¬ p4118) ∨ (¬ p4814))
    : p3256 ∨ (¬ p2518) ∨ (¬ p3878) ∨ (¬ p2475) ∨ (¬ p2088) ∨ (¬ p4814) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3878 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41511 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step81483 (p2254 p2331 p2518 p2528 p2963 p3379 p3461 p4604 p5274 p5284 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h62380 : (¬ p2254) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2963) ∨ (¬ p3379) ∨ (¬ p3461) ∨ (¬ p4604) ∨ (¬ p5274) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p2518) ∨ (¬ p5274) ∨ (¬ p2254) ∨ (¬ p3461) ∨ (¬ p2528) ∨ (¬ p3379) ∨ p2331 ∨ (¬ p4604) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h62380 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step81484 (p2406 p2475 p2518 p2901 p3238 p3961 p4283 p4320 p4702 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73374 : p3238 ∨ p2406)
    (h61692 : (¬ p2475) ∨ (¬ p2518) ∨ (¬ p3238) ∨ (¬ p3961) ∨ (¬ p4283) ∨ (¬ p4320) ∨ (¬ p4702))
    : (¬ p2518) ∨ p2901 ∨ (¬ p3961) ∨ (¬ p4283) ∨ (¬ p2475) ∨ (¬ p4702) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3961 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h61692 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step81485 (p2274 p2518 p2528 p2797 p2946 p2952 p3097 p3136 p3379 p3745 p4195 p4236 p4736 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73532 : p4195 ∨ p2797)
    (h73352 : p3097 ∨ p2274)
    (h54553 : (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2952) ∨ (¬ p3097) ∨ (¬ p3136) ∨ (¬ p3379) ∨ (¬ p3745) ∨ (¬ p4195) ∨ (¬ p4236) ∨ (¬ p4736))
    : (¬ p2518) ∨ p2946 ∨ (¬ p2528) ∨ p2797 ∨ (¬ p3379) ∨ (¬ p4236) ∨ (¬ p4736) ∨ p2274 ∨ (¬ p3136) ∨ (¬ p3745) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h54553 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step81489 (p2470 p2476 p2518 p2662 p2992 p3662 p4281 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73250 : p2476 ∨ p2470)
    (h69619 : (¬ p2518) ∨ (¬ p3662) ∨ (¬ p2476) ∨ (¬ p4281) ∨ (¬ p2662))
    : (¬ p2518) ∨ p2992 ∨ (¬ p4281) ∨ p2470 ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69619 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step81490 (p2437 p2518 p3083 p3379 p4256 : Prop)
    (h73542 : p4256 ∨ p3083)
    (h46649 : (¬ p2437) ∨ (¬ p2518) ∨ (¬ p3379) ∨ (¬ p4256))
    : (¬ p2518) ∨ p3083 ∨ (¬ p2437) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46649 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81493 (p2254 p2449 p2518 p2761 p2807 p3379 p3414 p3947 p4149 p4381 p5119 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73494 : p3947 ∨ p2449)
    (h73392 : p3414 ∨ p2807)
    (h53870 : (¬ p2254) ∨ (¬ p2518) ∨ (¬ p3379) ∨ (¬ p3414) ∨ (¬ p3947) ∨ (¬ p4149) ∨ (¬ p4381) ∨ (¬ p5119))
    : (¬ p4149) ∨ p2761 ∨ (¬ p2518) ∨ p2449 ∨ (¬ p3379) ∨ (¬ p2254) ∨ (¬ p5119) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4149 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h53870 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step81494 (p2254 p2264 p2518 p2528 p2807 p3379 p3414 p3553 p5118 p5558 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h73392 : p3414 ∨ p2807)
    (h58381 : (¬ p2254) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3379) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p5118) ∨ (¬ p5558))
    : (¬ p5558) ∨ (¬ p2518) ∨ (¬ p3379) ∨ p2264 ∨ (¬ p2528) ∨ (¬ p2254) ∨ (¬ p5118) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5558 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h58381 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step81498 (p2254 p2331 p2518 p2963 p3379 p3461 p3917 p4149 p4191 p4328 p5119 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73338 : p2963 ∨ p2331)
    (h57169 : (¬ p2254) ∨ (¬ p2518) ∨ (¬ p2963) ∨ (¬ p3379) ∨ (¬ p3917) ∨ (¬ p4149) ∨ (¬ p4191) ∨ (¬ p4328) ∨ (¬ p5119))
    : (¬ p4149) ∨ p3461 ∨ (¬ p2254) ∨ (¬ p3917) ∨ (¬ p3379) ∨ p2331 ∨ (¬ p2518) ∨ (¬ p4328) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4149 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h57169 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step81499 (p2518 p2651 p3364 p3641 p3874 p4116 p4790 : Prop)
    (h73484 : p3874 ∨ p3641)
    (h60197 : (¬ p2518) ∨ (¬ p2651) ∨ (¬ p3364) ∨ (¬ p3874) ∨ (¬ p4116) ∨ (¬ p4790))
    : (¬ p2518) ∨ (¬ p4116) ∨ (¬ p3364) ∨ (¬ p4790) ∨ (¬ p2651) ∨ p3641 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h60197 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step81502 (p2518 p2651 p3166 p3172 p4437 p4814 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h40959 : (¬ p2518) ∨ (¬ p2651) ∨ (¬ p3172) ∨ (¬ p4437) ∨ (¬ p4814))
    : (¬ p2518) ∨ p3166 ∨ (¬ p4437) ∨ (¬ p4814) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h40959 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step81503 (p2088 p2474 p2518 p2528 p3857 p5191 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h42177 : (¬ p2474) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3857) ∨ (¬ p5191))
    : (¬ p2518) ∨ (¬ p2528) ∨ p2088 ∨ (¬ p2474) ∨ (¬ p5191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2474 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42177 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step81509 (p2518 p2922 p2928 p3516 p3821 p4279 p4404 p4666 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73470 : p3821 ∨ p3516)
    (h57684 : (¬ p2518) ∨ (¬ p2928) ∨ (¬ p3821) ∨ (¬ p4279) ∨ (¬ p4404) ∨ (¬ p4666))
    : p2922 ∨ (¬ p2518) ∨ (¬ p4404) ∨ p3516 ∨ (¬ p4279) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4404 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4279 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h57684 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step81511 (p2254 p2331 p2363 p2518 p2922 p2928 p2963 p3256 p3389 p4079 p4118 p4196 p4596 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73520 : p4118 ∨ p3256)
    (h73338 : p2963 ∨ p2331)
    (h55174 : (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2518) ∨ (¬ p2928) ∨ (¬ p2963) ∨ (¬ p3389) ∨ (¬ p4079) ∨ (¬ p4118) ∨ (¬ p4196) ∨ (¬ p4596))
    : p2922 ∨ (¬ p3389) ∨ p3256 ∨ (¬ p2518) ∨ (¬ p2363) ∨ (¬ p4596) ∨ (¬ p4196) ∨ (¬ p4079) ∨ p2331 ∨ (¬ p2254) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4196 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h55174 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step81512 (p2449 p2518 p2528 p2685 p2696 p3365 p3379 p3572 p3947 p4669 p4736 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h73494 : p3947 ∨ p2449)
    (h73390 : p3365 ∨ p2696)
    (h49329 : (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3365) ∨ (¬ p3379) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4669) ∨ (¬ p4736))
    : (¬ p2518) ∨ (¬ p2528) ∨ (¬ p4669) ∨ p2685 ∨ p2449 ∨ (¬ p3379) ∨ (¬ p4736) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h49329 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step81513 (p2255 p2274 p2518 p2528 p2641 p2651 p2667 p3097 p3125 p3654 p3946 p4116 p4154 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73492 : p3946 ∨ p3654)
    (h73526 : p4154 ∨ p2641)
    (h52398 : (¬ p2255) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p2667) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p4116) ∨ (¬ p4154))
    : (¬ p2518) ∨ (¬ p4116) ∨ p2274 ∨ (¬ p2255) ∨ p3654 ∨ (¬ p2667) ∨ (¬ p2651) ∨ (¬ p2528) ∨ p2641 ∨ (¬ p3125) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h52398 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (False.elim (r8 u12)))))))))))))))))))))

theorem step81515 (p2098 p2104 p2241 p2247 p2363 p2518 p2744 p3366 p3379 p3609 p4340 p4596 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73558 : p4340 ∨ p3609)
    (h73204 : p2104 ∨ p2098)
    (h63743 : (¬ p2104) ∨ (¬ p2247) ∨ (¬ p2363) ∨ (¬ p2518) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3379) ∨ (¬ p4340) ∨ (¬ p4596))
    : p2241 ∨ p3609 ∨ (¬ p3366) ∨ (¬ p2363) ∨ (¬ p2744) ∨ p2098 ∨ (¬ p3379) ∨ (¬ p4596) ∨ (¬ p2518) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h63743 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step81553 (p2696 p2753 p2797 p3073 p3323 p3379 p3449 p3860 p4261 p4330 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h73544 : p4261 ∨ p3073)
    (h71504 : (¬ p3860) ∨ (¬ p3379) ∨ (¬ p2696) ∨ (¬ p4330) ∨ (¬ p4261) ∨ (¬ p3323) ∨ (¬ p2753) ∨ (¬ p2797))
    : p3449 ∨ (¬ p2753) ∨ (¬ p2797) ∨ (¬ p4330) ∨ (¬ p3379) ∨ (¬ p2696) ∨ (¬ p3323) ∨ p3073 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3449) := (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h71504 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step81557 (p2573 p2579 p2685 p2696 p2753 p3347 p3461 p3564 p3931 p4137 p4191 p4826 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73274 : p2579 ∨ p2573)
    (h73524 : p4137 ∨ p3564)
    (h71506 : (¬ p4137) ∨ (¬ p4191) ∨ (¬ p2696) ∨ (¬ p4826) ∨ (¬ p2579) ∨ (¬ p2685) ∨ (¬ p3347) ∨ (¬ p3931) ∨ (¬ p2753))
    : (¬ p3931) ∨ p3461 ∨ (¬ p2685) ∨ (¬ p4826) ∨ p2573 ∨ (¬ p2696) ∨ (¬ p3347) ∨ p3564 ∨ (¬ p2753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3931 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h71506 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step81559 (p2187 p2437 p2753 p3125 p3343 p3362 p3389 p3742 p3744 p3923 p4870 p5322 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73454 : p3744 ∨ p3125)
    (h62647 : (¬ p2187) ∨ (¬ p2753) ∨ (¬ p3343) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p3744) ∨ (¬ p3923) ∨ (¬ p4870) ∨ (¬ p5322))
    : (¬ p3343) ∨ (¬ p3389) ∨ (¬ p5322) ∨ (¬ p2753) ∨ p2437 ∨ (¬ p3362) ∨ (¬ p4870) ∨ (¬ p2187) ∨ p3125 ∨ (¬ p3923) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h62647 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step81572 (p2122 p2252 p2651 p2657 p2750 p2753 p2774 p3276 p3343 p3359 p3791 p4425 p4826 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73288 : p2657 ∨ p2651)
    (h73388 : p3359 ∨ p3343)
    (h57217 : (¬ p2122) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3359) ∨ (¬ p3791) ∨ (¬ p4425) ∨ (¬ p4826))
    : p3276 ∨ (¬ p4826) ∨ (¬ p2122) ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p2753) ∨ (¬ p2774) ∨ p2651 ∨ p3343 ∨ (¬ p3791) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h57217 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u1)))))))))))))))))))))

theorem step81575 (p2156 p2598 p2753 p3125 p3201 p3461 p3645 p3646 p3744 p3868 p4191 p4826 p4877 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73436 : p3646 ∨ p2156)
    (h73454 : p3744 ∨ p3125)
    (h51308 : (¬ p2598) ∨ (¬ p2753) ∨ (¬ p3201) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p3868) ∨ (¬ p4191) ∨ (¬ p4826) ∨ (¬ p4877))
    : (¬ p3868) ∨ (¬ p2753) ∨ (¬ p3201) ∨ (¬ p2598) ∨ p3461 ∨ (¬ p4877) ∨ p2156 ∨ (¬ p3645) ∨ (¬ p4826) ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3868 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h51308 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step81583 (p2166 p2191 p2210 p2363 p2753 p3166 p3256 p3379 p3555 p4117 p4134 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73222 : p2191 ∨ p2166)
    (h73412 : p3555 ∨ p2210)
    (h71512 : (¬ p4347) ∨ (¬ p2191) ∨ (¬ p2753) ∨ (¬ p3379) ∨ (¬ p3166) ∨ (¬ p3555) ∨ (¬ p4117) ∨ (¬ p3256) ∨ (¬ p4134))
    : (¬ p2753) ∨ p2363 ∨ (¬ p4134) ∨ p2166 ∨ (¬ p3379) ∨ (¬ p3256) ∨ (¬ p4117) ∨ (¬ p3166) ∨ p2210 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2753 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2191 := (Or.elim h73222 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h71512 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step81585 (p2122 p2177 p2753 p2774 p3246 p3379 p3399 p3690 p4366 p4666 p4909 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73446 : p3690 ∨ p3246)
    (h71513 : (¬ p3690) ∨ (¬ p4909) ∨ (¬ p2774) ∨ (¬ p3379) ∨ (¬ p2753) ∨ (¬ p4366) ∨ (¬ p4666) ∨ (¬ p2177) ∨ (¬ p2122))
    : p3399 ∨ p3246 ∨ (¬ p2177) ∨ (¬ p4909) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p4666) ∨ (¬ p2122) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4909 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71513 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step81586 (p2598 p2753 p3367 p3585 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h5210 : (¬ p2598) ∨ (¬ p2753) ∨ (¬ p3585))
    : (¬ p2753) ∨ p3367 ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2753 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3367) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h5210 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u3)))))))

theorem step81589 (p2132 p2753 p2870 p2881 p3379 p3399 p4366 p4442 p5559 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h71515 : (¬ p4442) ∨ (¬ p2132) ∨ (¬ p2870) ∨ (¬ p4366) ∨ (¬ p3379) ∨ (¬ p5559) ∨ (¬ p2753) ∨ (¬ p2881))
    : (¬ p2753) ∨ (¬ p3379) ∨ (¬ p2870) ∨ (¬ p2881) ∨ p3399 ∨ (¬ p2132) ∨ (¬ p5559) ∨ (¬ p4442) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2753 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4442 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h71515 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step81590 (p2230 p2427 p2589 p2870 p3582 p4235 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73284 : p2589 ∨ p2230)
    (h71516 : (¬ p3582) ∨ (¬ p4235) ∨ (¬ p2589) ∨ (¬ p2870))
    : (¬ p2870) ∨ p2427 ∨ (¬ p3582) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3582 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71516 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step81591 (p2230 p2373 p2589 p2619 p3347 p3582 p3880 p5214 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73284 : p2589 ∨ p2230)
    (h42436 : (¬ p2589) ∨ (¬ p2619) ∨ (¬ p3347) ∨ (¬ p3582) ∨ (¬ p3880) ∨ (¬ p5214))
    : (¬ p2619) ∨ (¬ p3582) ∨ (¬ p5214) ∨ p2373 ∨ (¬ p3347) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3582 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5214 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h42436 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step81592 (p2156 p2440 p2860 p3582 p3646 p4031 p4753 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h49012 : (¬ p2440) ∨ (¬ p2860) ∨ (¬ p3582) ∨ (¬ p3646) ∨ (¬ p4031) ∨ (¬ p4753))
    : (¬ p4031) ∨ (¬ p3582) ∨ (¬ p2860) ∨ p2156 ∨ (¬ p2440) ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4031 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3582 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49012 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step81595 (p2440 p2870 p3051 p3556 p3582 p4031 p4753 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h42204 : (¬ p2440) ∨ (¬ p2870) ∨ (¬ p3556) ∨ (¬ p3582) ∨ (¬ p4031) ∨ (¬ p4753))
    : (¬ p2870) ∨ p3051 ∨ (¬ p4031) ∨ (¬ p4753) ∨ (¬ p3582) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3582 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42204 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step81596 (p2440 p2563 p2860 p3582 p4110 p4753 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h61810 : (¬ p2440) ∨ (¬ p2860) ∨ (¬ p3582) ∨ (¬ p4110) ∨ (¬ p4753))
    : (¬ p3582) ∨ (¬ p2440) ∨ p2563 ∨ (¬ p2860) ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3582 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h61810 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step81599 (p2132 p2138 p2598 p3055 p3582 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73349 : (¬ p2598) ∨ (¬ p3055))
    (h26990 : (¬ p2138) ∨ p3055 ∨ (¬ p3582))
    : p2132 ∨ (¬ p3582) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p3582 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p3055) := (Or.elim h73349 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h26990 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step81605 (p2870 p2901 p2946 p2952 p3475 p3582 p4320 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73330 : p2952 ∨ p2946)
    (h71518 : (¬ p3582) ∨ (¬ p4320) ∨ (¬ p2870) ∨ (¬ p3475) ∨ (¬ p2952))
    : p2901 ∨ p2946 ∨ (¬ p3582) ∨ (¬ p2870) ∨ (¬ p3475) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3582 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71518 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step81606 (p2230 p2373 p2589 p2619 p3201 p3582 p3876 p3880 p3905 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73284 : p2589 ∨ p2230)
    (h73486 : p3876 ∨ p3201)
    (h50826 : (¬ p2589) ∨ (¬ p2619) ∨ (¬ p3582) ∨ (¬ p3876) ∨ (¬ p3880) ∨ (¬ p3905))
    : (¬ p3582) ∨ (¬ p2619) ∨ (¬ p3905) ∨ p2373 ∨ p2230 ∨ p3201 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3582 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u8 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h50826 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step81607 (p2427 p2563 p2598 p2870 p3582 p4235 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h62806 : (¬ p2563) ∨ (¬ p2598) ∨ (¬ p2870) ∨ (¬ p3582) ∨ (¬ p4235))
    : (¬ p2870) ∨ p2427 ∨ (¬ p2563) ∨ (¬ p2598) ∨ (¬ p3582) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3582 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h62806 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step81608 (p2406 p2427 p2870 p3238 p3582 p4235 p5214 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h73536 : p4235 ∨ p2427)
    (h59968 : (¬ p2870) ∨ (¬ p3238) ∨ (¬ p3582) ∨ (¬ p4235) ∨ (¬ p5214))
    : (¬ p2870) ∨ (¬ p3582) ∨ p2406 ∨ (¬ p5214) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3582 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5214 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h59968 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step81609 (p2373 p2563 p2598 p2619 p3582 p3880 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h62807 : (¬ p2563) ∨ (¬ p2598) ∨ (¬ p2619) ∨ (¬ p3582) ∨ (¬ p3880))
    : (¬ p2619) ∨ (¬ p3582) ∨ (¬ p2563) ∨ p2373 ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3582 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62807 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step81610 (p2373 p2619 p3422 p3582 p3584 p3880 p4715 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h73490 : p3880 ∨ p2373)
    (h57959 : (¬ p2619) ∨ (¬ p3582) ∨ (¬ p3584) ∨ (¬ p3880) ∨ (¬ p4715))
    : (¬ p2619) ∨ (¬ p3582) ∨ (¬ p4715) ∨ p3422 ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3582 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h57959 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step81614 (p2839 p3367 p3582 p3583 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h5207 : (¬ p3367) ∨ (¬ p3582) ∨ (¬ p3583))
    : (¬ p3367) ∨ p2839 ∨ (¬ p3582) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3582 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h5207 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step81620 (p2132 p2138 p2608 p2707 p3582 p3873 p5086 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h41053 : (¬ p2138) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p3582) ∨ (¬ p3873) ∨ (¬ p5086))
    : (¬ p3873) ∨ p2132 ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p5086) ∨ (¬ p3582) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3873 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5086 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3582 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41053 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step81625 (p2619 p2850 p3096 p3422 p3582 p3584 p4509 p4715 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h65956 : (¬ p3584) ∨ (¬ p3582) ∨ (¬ p2850) ∨ (¬ p4715) ∨ (¬ p3096) ∨ (¬ p4509) ∨ (¬ p2619))
    : p3422 ∨ (¬ p2619) ∨ (¬ p3096) ∨ (¬ p2850) ∨ (¬ p4715) ∨ (¬ p3582) ∨ (¬ p4509) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3582 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h65956 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u1)))))))))))))))

theorem step81627 (p2870 p3051 p3422 p3556 p3582 p3584 p4031 p4715 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73426 : p3584 ∨ p3422)
    (h52753 : (¬ p2870) ∨ (¬ p3556) ∨ (¬ p3582) ∨ (¬ p3584) ∨ (¬ p4031) ∨ (¬ p4715))
    : (¬ p2870) ∨ p3051 ∨ p3422 ∨ (¬ p3582) ∨ (¬ p4031) ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3582 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52753 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step81629 (p2427 p2870 p3422 p3582 p3584 p4235 p4715 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h73536 : p4235 ∨ p2427)
    (h48366 : (¬ p2870) ∨ (¬ p3582) ∨ (¬ p3584) ∨ (¬ p4235) ∨ (¬ p4715))
    : (¬ p3582) ∨ p3422 ∨ p2427 ∨ (¬ p2870) ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3582 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48366 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step81631 (p2982 p3105 p3422 p3582 p3584 p4715 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h73426 : p3584 ∨ p3422)
    (h57132 : (¬ p3105) ∨ (¬ p3582) ∨ (¬ p3584) ∨ (¬ p4715) ∨ (¬ p4948))
    : (¬ p3105) ∨ (¬ p3582) ∨ p2982 ∨ (¬ p4715) ∨ p3422 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3582 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h57132 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step81640 (p3193 p3222 p3346 p3347 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h4809 : (¬ p3222) ∨ (¬ p3346) ∨ (¬ p3347))
    : p3193 ∨ (¬ p3346) ∨ (¬ p3347) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h4809 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step81641 (p2911 p2922 p2928 p3193 p3222 p3644 p4451 p4668 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73434 : p3644 ∨ p2911)
    (h73320 : p2928 ∨ p2922)
    (h49730 : (¬ p2928) ∨ (¬ p3222) ∨ (¬ p3644) ∨ (¬ p4451) ∨ (¬ p4668))
    : p3193 ∨ (¬ p4451) ∨ p2911 ∨ (¬ p4668) ∨ p2922 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p4451 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49730 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step81642 (p2922 p2928 p3193 p3222 p3276 p3389 p4079 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73320 : p2928 ∨ p2922)
    (h46530 : (¬ p2928) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3389) ∨ (¬ p4079))
    : (¬ p3389) ∨ p3193 ∨ p2922 ∨ (¬ p3276) ∨ (¬ p4079) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3193) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46530 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step81643 (p2406 p3193 p3222 p3238 p3346 p3389 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73374 : p3238 ∨ p2406)
    (h46576 : (¬ p3222) ∨ (¬ p3238) ∨ (¬ p3346) ∨ (¬ p3389))
    : p3193 ∨ (¬ p3346) ∨ (¬ p3389) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46576 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step81645 (p2440 p2542 p3193 p3222 p3343 p3359 p3379 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73388 : p3359 ∨ p3343)
    (h73270 : p2542 ∨ p2440)
    (h51871 : (¬ p2542) ∨ (¬ p3222) ∨ (¬ p3359) ∨ (¬ p3379))
    : p3193 ∨ p3343 ∨ p2440 ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h51871 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step81648 (p2254 p2284 p2946 p2952 p3193 p3222 p3276 p3379 p3952 p4393 p5254 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73496 : p3952 ∨ p2284)
    (h73330 : p2952 ∨ p2946)
    (h59535 : (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3379) ∨ (¬ p3952) ∨ (¬ p4393) ∨ (¬ p5254))
    : (¬ p4393) ∨ p3193 ∨ (¬ p2254) ∨ (¬ p3379) ∨ (¬ p3276) ∨ p2284 ∨ p2946 ∨ (¬ p5254) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4393 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3193) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h59535 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step81649 (p2210 p3193 p3222 p3346 p3541 p4108 p4877 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h50769 : (¬ p2210) ∨ (¬ p3222) ∨ (¬ p3346) ∨ (¬ p3541) ∨ (¬ p4108) ∨ (¬ p4877))
    : p3193 ∨ (¬ p3346) ∨ (¬ p2210) ∨ (¬ p4877) ∨ (¬ p3541) ∨ (¬ p4108) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h50769 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step81650 (p3193 p3222 p3343 p3359 p4116 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73388 : p3359 ∨ p3343)
    (h6151 : (¬ p3222) ∨ (¬ p3359) ∨ (¬ p4116))
    : p3193 ∨ p3343 ∨ (¬ p4116) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h6151 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u2)))))))

theorem step81651 (p2437 p2761 p2922 p2928 p3193 p3222 p4451 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73320 : p2928 ∨ p2922)
    (h56920 : (¬ p2437) ∨ (¬ p2761) ∨ (¬ p2928) ∨ (¬ p3222) ∨ (¬ p4451))
    : p3193 ∨ p2922 ∨ (¬ p2437) ∨ (¬ p2761) ∨ (¬ p4451) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2922) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4451 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h56920 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step81653 (p2427 p2891 p3193 p3222 p3486 p4202 p4953 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73398 : p3486 ∨ p2891)
    (h41510 : (¬ p2427) ∨ (¬ p3222) ∨ (¬ p3486) ∨ (¬ p4202) ∨ (¬ p4953))
    : (¬ p4953) ∨ p3193 ∨ (¬ p2427) ∨ p2891 ∨ (¬ p4202) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4953 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3193) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41510 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step81656 (p2922 p2928 p3193 p3222 p3246 p3690 p4451 p4647 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73320 : p2928 ∨ p2922)
    (h73446 : p3690 ∨ p3246)
    (h50014 : (¬ p2928) ∨ (¬ p3222) ∨ (¬ p3690) ∨ (¬ p4451) ∨ (¬ p4647))
    : p3193 ∨ (¬ p4451) ∨ p2922 ∨ (¬ p4647) ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p4451 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50014 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step81657 (p2396 p2922 p2928 p3193 p3222 p4107 p4451 p4712 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73514 : p4107 ∨ p2396)
    (h73320 : p2928 ∨ p2922)
    (h50387 : (¬ p2928) ∨ (¬ p3222) ∨ (¬ p4107) ∨ (¬ p4451) ∨ (¬ p4712))
    : p3193 ∨ (¬ p4451) ∨ p2396 ∨ p2922 ∨ (¬ p4712) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p4451 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50387 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step81665 (p2406 p3193 p3222 p3237 p3238 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73374 : p3238 ∨ p2406)
    (h4597 : (¬ p3222) ∨ (¬ p3237) ∨ (¬ p3238))
    : p3193 ∨ (¬ p3237) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p3237 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h4597 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step81667 (p2230 p2406 p3193 p3222 p3238 p3276 p4079 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73374 : p3238 ∨ p2406)
    (h49347 : (¬ p2230) ∨ (¬ p3222) ∨ (¬ p3238) ∨ (¬ p3276) ∨ (¬ p4079))
    : p3193 ∨ (¬ p3276) ∨ p2406 ∨ (¬ p2230) ∨ (¬ p4079) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h49347 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step81672 (p2098 p2104 p2363 p2922 p2928 p3193 p3222 p3389 p3609 p3657 p4079 p4340 p4451 p4503 p4736 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73558 : p4340 ∨ p3609)
    (h73320 : p2928 ∨ p2922)
    (h73204 : p2104 ∨ p2098)
    (h63489 : (¬ p2104) ∨ (¬ p2363) ∨ (¬ p2928) ∨ (¬ p3222) ∨ (¬ p3389) ∨ (¬ p3657) ∨ (¬ p4079) ∨ (¬ p4340) ∨ (¬ p4451) ∨ (¬ p4503) ∨ (¬ p4736))
    : (¬ p3389) ∨ p3193 ∨ (¬ p4079) ∨ p3609 ∨ (¬ p4451) ∨ p2922 ∨ (¬ p4503) ∨ (¬ p4736) ∨ (¬ p3657) ∨ p2098 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3193) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4451 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u14 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h63489 (fun q0 => (False.elim (q0 u14))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u13))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step81673 (p2608 p3193 p3222 p3276 p3379 p3954 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73498 : p3954 ∨ p2608)
    (h46657 : (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3379) ∨ (¬ p3954))
    : p3193 ∨ p2608 ∨ (¬ p3276) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46657 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step81677 (p2927 p3193 p3222 p3379 p3399 p4366 p4640 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73570 : p4366 ∨ p3399)
    (h51475 : (¬ p2927) ∨ (¬ p3222) ∨ (¬ p3379) ∨ (¬ p4366) ∨ (¬ p4640))
    : p3193 ∨ p3399 ∨ (¬ p2927) ∨ (¬ p4640) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2927 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4640 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h51475 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step81681 (p2641 p2662 p3193 p3222 p3346 p4154 p4281 p4972 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73526 : p4154 ∨ p2641)
    (h42473 : (¬ p2662) ∨ (¬ p3222) ∨ (¬ p3346) ∨ (¬ p4154) ∨ (¬ p4281) ∨ (¬ p4972))
    : p3193 ∨ p2641 ∨ (¬ p2662) ∨ (¬ p3346) ∨ (¬ p4281) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42473 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step81682 (p2245 p2651 p2657 p2922 p2928 p3193 p3222 p3343 p3359 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73388 : p3359 ∨ p3343)
    (h73320 : p2928 ∨ p2922)
    (h73288 : p2657 ∨ p2651)
    (h44691 : (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2928) ∨ (¬ p3222) ∨ (¬ p3359))
    : p3193 ∨ (¬ p2245) ∨ p3343 ∨ p2922 ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h44691 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step81685 (p2406 p2619 p3193 p3222 p3238 p3694 p4335 p4882 p4952 : Prop)
    (h73450 : p3694 ∨ p2619)
    (h73374 : p3238 ∨ p2406)
    (h73364 : p3222 ∨ p3193)
    (h50053 : (¬ p3222) ∨ (¬ p3238) ∨ (¬ p3694) ∨ (¬ p4335) ∨ (¬ p4882) ∨ (¬ p4952))
    : (¬ p4335) ∨ p2619 ∨ (¬ p4882) ∨ p2406 ∨ (¬ p4952) ∨ p3193 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4335 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4882 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3193) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3694 := (Or.elim h73450 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h50053 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step81687 (p2493 p2499 p2573 p3193 p3222 p3276 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73260 : p2499 ∨ p2493)
    (h58735 : (¬ p2499) ∨ (¬ p2573) ∨ (¬ p3222) ∨ (¬ p3276))
    : p3193 ∨ (¬ p3276) ∨ (¬ p2573) ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h58735 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step81691 (p2493 p2499 p2553 p2588 p3193 p3222 p4331 p4624 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73282 : p2588 ∨ p2553)
    (h73260 : p2499 ∨ p2493)
    (h50365 : (¬ p2499) ∨ (¬ p2588) ∨ (¬ p3222) ∨ (¬ p4331) ∨ (¬ p4624))
    : p3193 ∨ (¬ p4331) ∨ (¬ p4624) ∨ p2553 ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p4331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4624 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50365 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step81702 (p2088 p2478 p2509 p3193 p3222 p3857 p4695 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73480 : p3857 ∨ p2088)
    (h41387 : (¬ p2478) ∨ (¬ p2509) ∨ (¬ p3222) ∨ (¬ p3857) ∨ (¬ p4695))
    : (¬ p2509) ∨ p3193 ∨ p2088 ∨ (¬ p2478) ∨ (¬ p4695) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3193) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2478 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41387 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step81704 (p2493 p2499 p3193 p3222 p3917 p4331 p5222 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73260 : p2499 ∨ p2493)
    (h64501 : (¬ p2499) ∨ (¬ p3222) ∨ (¬ p3917) ∨ (¬ p4331) ∨ (¬ p5222))
    : p3193 ∨ (¬ p4331) ∨ (¬ p5222) ∨ p2493 ∨ (¬ p3917) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p4331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h64501 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step81705 (p2493 p2499 p2581 p3193 p3222 p3654 p3946 p4331 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73492 : p3946 ∨ p3654)
    (h73260 : p2499 ∨ p2493)
    (h48605 : (¬ p2499) ∨ (¬ p2581) ∨ (¬ p3222) ∨ (¬ p3946) ∨ (¬ p4331))
    : p3193 ∨ (¬ p4331) ∨ (¬ p2581) ∨ p3654 ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p4331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48605 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step81708 (p3193 p3222 p3266 p3276 p3379 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73364 : p3222 ∨ p3193)
    (h45265 : (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3379) ∨ (¬ p4444))
    : p3266 ∨ (¬ p3276) ∨ (¬ p3379) ∨ p3193 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3193) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45265 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81709 (p2761 p3193 p3222 p3276 p3379 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73364 : p3222 ∨ p3193)
    (h45276 : (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3379) ∨ (¬ p4381))
    : p2761 ∨ p3193 ∨ (¬ p3276) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3193) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45276 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81715 (p2241 p2247 p3193 p3222 p3343 p3359 p3379 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73388 : p3359 ∨ p3343)
    (h73226 : p2247 ∨ p2241)
    (h45108 : (¬ p2247) ∨ (¬ p3222) ∨ (¬ p3359) ∨ (¬ p3379))
    : p3193 ∨ p3343 ∨ p2241 ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45108 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step81716 (p2662 p2992 p3193 p3222 p3346 p3662 p4281 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73364 : p3222 ∨ p3193)
    (h69620 : (¬ p3222) ∨ (¬ p3662) ∨ (¬ p2662) ∨ (¬ p4281) ∨ (¬ p3346))
    : p2992 ∨ p3193 ∨ (¬ p3346) ∨ (¬ p4281) ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3193) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h69620 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step81722 (p2187 p2493 p2499 p3193 p3222 p3989 p4045 p4157 p4718 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73502 : p3989 ∨ p2187)
    (h73260 : p2499 ∨ p2493)
    (h60955 : (¬ p2499) ∨ (¬ p3222) ∨ (¬ p3989) ∨ (¬ p4045) ∨ (¬ p4157) ∨ (¬ p4718))
    : p3193 ∨ (¬ p4045) ∨ (¬ p4718) ∨ (¬ p4157) ∨ p2187 ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p4045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u8 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h60955 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step81725 (p2774 p2780 p2819 p3193 p3222 p3276 p3379 p4358 p4736 p5123 p5580 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h73308 : p2780 ∨ p2774)
    (h73364 : p3222 ∨ p3193)
    (h50937 : (¬ p2780) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3379) ∨ (¬ p4358) ∨ (¬ p4736) ∨ (¬ p5123) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p5123) ∨ (¬ p3379) ∨ p2819 ∨ (¬ p4736) ∨ p2774 ∨ p3193 ∨ (¬ p3276) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3193) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h50937 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step81727 (p2254 p2331 p2668 p2963 p3193 p3222 p3276 p3324 p3379 p5123 p5580 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73364 : p3222 ∨ p3193)
    (h73386 : p3324 ∨ p2668)
    (h49081 : (¬ p2254) ∨ (¬ p2963) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3324) ∨ (¬ p3379) ∨ (¬ p5123) ∨ (¬ p5580))
    : (¬ p5580) ∨ p2331 ∨ (¬ p2254) ∨ p3193 ∨ (¬ p5123) ∨ p2668 ∨ (¬ p3276) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3193) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h49081 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step81734 (p2122 p2253 p2651 p2774 p2780 p3193 p3222 p3276 p3822 p4116 p4260 p4736 p4831 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73472 : p3822 ∨ p2122)
    (h73364 : p3222 ∨ p3193)
    (h60412 : (¬ p2253) ∨ (¬ p2651) ∨ (¬ p2780) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3822) ∨ (¬ p4116) ∨ (¬ p4260) ∨ (¬ p4736) ∨ (¬ p4831))
    : (¬ p4260) ∨ p2774 ∨ p2122 ∨ (¬ p2651) ∨ (¬ p4831) ∨ (¬ p3276) ∨ (¬ p4736) ∨ p3193 ∨ (¬ p2253) ∨ (¬ p4116) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4260 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3193) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h60412 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step81735 (p2406 p2563 p3193 p3222 p3238 p4110 p4952 p5046 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73374 : p3238 ∨ p2406)
    (h73516 : p4110 ∨ p2563)
    (h49239 : (¬ p3222) ∨ (¬ p3238) ∨ (¬ p4110) ∨ (¬ p4952) ∨ (¬ p5046))
    : (¬ p4952) ∨ p3193 ∨ (¬ p5046) ∨ p2406 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4952 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3193) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5046 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49239 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step81738 (p2608 p3379 p3452 p3541 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h5163 : (¬ p2608) ∨ (¬ p3452) ∨ (¬ p3541))
    : p3379 ∨ (¬ p2608) ∨ (¬ p3541) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h5163 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step81739 (p2608 p3379 p3452 p3541 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h20684 : (¬ p2608) ∨ (¬ p3452) ∨ (¬ p3541))
    : p3379 ∨ (¬ p2608) ∨ (¬ p3541) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h20684 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step81741 (p2406 p2440 p2696 p2737 p2743 p3541 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h51920 : (¬ p2406) ∨ (¬ p2440) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3541))
    : p2737 ∨ (¬ p2406) ∨ (¬ p2696) ∨ (¬ p3541) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h51920 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step81742 (p2230 p2406 p2573 p2589 p2737 p2743 p3541 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73284 : p2589 ∨ p2230)
    (h52200 : (¬ p2406) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p2743) ∨ (¬ p3541))
    : p2737 ∨ (¬ p3541) ∨ p2230 ∨ (¬ p2406) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52200 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step81745 (p2230 p2406 p2589 p2655 p2829 p3361 p3541 p3688 p4842 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73284 : p2589 ∨ p2230)
    (h42034 : (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p3361) ∨ (¬ p3541) ∨ (¬ p3688) ∨ (¬ p4842))
    : p2829 ∨ (¬ p3541) ∨ p2230 ∨ (¬ p4842) ∨ (¬ p2406) ∨ (¬ p3361) ∨ (¬ p2655) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42034 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step81746 (p2737 p2743 p2922 p3363 p3389 p3540 p3541 p4752 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73402 : p3540 ∨ p3389)
    (h51803 : (¬ p2743) ∨ (¬ p2922) ∨ (¬ p3363) ∨ (¬ p3540) ∨ (¬ p3541) ∨ (¬ p4752))
    : p2737 ∨ (¬ p3541) ∨ (¬ p4752) ∨ p3389 ∨ (¬ p3363) ∨ (¬ p2922) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h51803 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step81748 (p2440 p2542 p2662 p2737 p2743 p2922 p3389 p3540 p3541 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h73270 : p2542 ∨ p2440)
    (h73298 : p2743 ∨ p2737)
    (h45496 : (¬ p2542) ∨ (¬ p2662) ∨ (¬ p2743) ∨ (¬ p2922) ∨ (¬ p3540) ∨ (¬ p3541))
    : (¬ p2922) ∨ (¬ p2662) ∨ p3389 ∨ (¬ p3541) ∨ p2440 ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u8 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h45496 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step81752 (p3641 p3874 p4045 p5160 : Prop)
    (h73484 : p3874 ∨ p3641)
    (h28616 : (¬ p3874) ∨ (¬ p4045) ∨ p5160)
    : p5160 ∨ (¬ p4045) ∨ p3641 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5160) := (fun h => hn (Or.inl h));
    let u1 : p4045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h28616 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step81759 (p2241 p2247 p2598 p2744 p3367 p3585 p3589 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73428 : p3585 ∨ p3367)
    (h41006 : (¬ p2247) ∨ (¬ p2598) ∨ (¬ p2744) ∨ (¬ p3585) ∨ (¬ p3589))
    : (¬ p3589) ∨ p2241 ∨ p3367 ∨ (¬ p2744) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41006 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step81762 (p2210 p2598 p3367 p3555 p3585 p3589 p4377 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h73412 : p3555 ∨ p2210)
    (h60038 : (¬ p2598) ∨ (¬ p3555) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p4377))
    : p3367 ∨ p2210 ∨ (¬ p3589) ∨ (¬ p4377) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3367) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h60038 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step81764 (p2449 p2696 p2707 p2737 p2743 p3589 p4325 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h54673 : (¬ p2449) ∨ (¬ p2696) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p3589) ∨ (¬ p4325))
    : p2737 ∨ (¬ p2707) ∨ (¬ p2696) ∨ (¬ p3589) ∨ (¬ p2449) ∨ (¬ p4325) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h54673 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step81765 (p2696 p2737 p2743 p3379 p3452 p3589 p4376 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73394 : p3452 ∨ p3379)
    (h52156 : (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3452) ∨ (¬ p3589) ∨ (¬ p4376))
    : p2737 ∨ p3379 ∨ (¬ p2696) ∨ (¬ p4376) ∨ (¬ p3589) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h52156 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step81767 (p2598 p2707 p2911 p3367 p3585 p3589 p3658 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h43185 : (¬ p2598) ∨ (¬ p2707) ∨ (¬ p2911) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p3658))
    : (¬ p2707) ∨ (¬ p2911) ∨ (¬ p3658) ∨ (¬ p3589) ∨ (¬ p2598) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3658 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h43185 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step81769 (p2177 p2254 p2264 p2598 p2707 p2807 p3367 p3414 p3553 p3585 p3589 p4473 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h73392 : p3414 ∨ p2807)
    (h73410 : p3553 ∨ p2264)
    (h53551 : (¬ p2177) ∨ (¬ p2254) ∨ (¬ p2598) ∨ (¬ p2707) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p4473))
    : (¬ p3589) ∨ p3367 ∨ p2807 ∨ (¬ p2598) ∨ (¬ p2254) ∨ p2264 ∨ (¬ p2177) ∨ (¬ p2707) ∨ (¬ p4473) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3367) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4473 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h53551 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step81771 (p2598 p3093 p3367 p3585 p3589 p3591 p4866 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73428 : p3585 ∨ p3367)
    (h60039 : (¬ p2598) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p3591) ∨ (¬ p4866))
    : p3093 ∨ (¬ p4866) ∨ (¬ p2598) ∨ p3367 ∨ (¬ p3589) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p4866 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60039 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step81772 (p2696 p2742 p3093 p3589 p3591 p4759 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h26666 : (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3589) ∨ (¬ p3591) ∨ (¬ p4759))
    : (¬ p2742) ∨ p3093 ∨ (¬ p3589) ∨ (¬ p2696) ∨ (¬ p4759) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2742 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h26666 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step81777 (p2774 p2780 p3093 p3589 p3591 p3918 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73307 : (¬ p2774) ∨ (¬ p2780))
    (h39321 : p2780 ∨ (¬ p3589) ∨ (¬ p3591) ∨ (¬ p3918))
    : (¬ p3918) ∨ p3093 ∨ (¬ p3589) ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3918 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : (¬ p2780) := (Or.elim h73307 (fun q0 => (False.elim (q0 u3))) (fun r0 => r0));
    (Or.elim h39321 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step81783 (p2230 p2589 p2598 p3237 p3333 p3589 p5193 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h53375 : (¬ p2589) ∨ (¬ p2598) ∨ (¬ p3237) ∨ (¬ p3333) ∨ (¬ p3589) ∨ (¬ p5193))
    : (¬ p3333) ∨ (¬ p3237) ∨ (¬ p5193) ∨ (¬ p2598) ∨ (¬ p3589) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3237 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h53375 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step81784 (p2598 p3367 p3379 p3452 p3585 p3589 p4376 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h73394 : p3452 ∨ p3379)
    (h49300 : (¬ p2598) ∨ (¬ p3452) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p4376))
    : p3367 ∨ p3379 ∨ (¬ p4376) ∨ (¬ p3589) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3367) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h49300 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step81788 (p2132 p2737 p2839 p3583 p3589 p3830 p3834 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h73424 : p3583 ∨ p2839)
    (h45927 : (¬ p2132) ∨ (¬ p2737) ∨ (¬ p3583) ∨ (¬ p3589) ∨ (¬ p3834))
    : p3830 ∨ p2839 ∨ (¬ p2737) ∨ (¬ p3589) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45927 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step81796 (p2427 p2598 p2839 p3367 p3585 p3589 p3695 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h42817 : (¬ p2427) ∨ (¬ p2598) ∨ (¬ p2839) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p3695))
    : (¬ p3695) ∨ (¬ p2839) ∨ (¬ p3589) ∨ (¬ p2427) ∨ p3367 ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3695 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42817 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step81797 (p2528 p2598 p3367 p3537 p3585 p3589 p5373 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h42837 : (¬ p2528) ∨ (¬ p2598) ∨ (¬ p3537) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p5373))
    : (¬ p3537) ∨ (¬ p5373) ∨ p3367 ∨ (¬ p3589) ∨ (¬ p2598) ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3537 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42837 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step81800 (p2696 p4236 p4785 : Prop)
    (h73758 : p4785 ∨ p2696)
    (h7803 : p4236 ∨ (¬ p4785))
    : p4236 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4236) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr h));
    let u2 : p4785 := (Or.elim h73758 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h7803 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step81801 (p2696 p2811 p4785 : Prop)
    (h73758 : p4785 ∨ p2696)
    (h7804 : p2811 ∨ (¬ p4785))
    : p2811 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2811) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr h));
    let u2 : p4785 := (Or.elim h73758 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h7804 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step81802 (p2696 p4785 p4786 : Prop)
    (h73758 : p4785 ∨ p2696)
    (h7806 : (¬ p4785) ∨ p4786)
    : p2696 ∨ p4786 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2696) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4786) := (fun h => hn (Or.inr h));
    let u2 : p4785 := (Or.elim h73758 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7806 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step81804 (p2177 p2331 p2396 p2440 p2563 p2630 p2696 p2737 p2747 p2810 p2881 p2946 p2963 p4500 p4619 p4703 p4714 p4785 p4903 : Prop)
    (h73820 : p4903 ∨ (¬ p2881))
    (h73316 : p2810 ∨ p2630)
    (h73338 : p2963 ∨ p2331)
    (h73672 : p4619 ∨ p2396)
    (h73302 : p2747 ∨ (¬ p2737))
    (h73714 : p4703 ∨ p2440)
    (h73602 : p4500 ∨ p2177)
    (h73758 : p4785 ∨ p2696)
    (h73720 : p4714 ∨ p2563)
    (h66744 : (¬ p4785) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p4714) ∨ (¬ p4703) ∨ (¬ p4903) ∨ (¬ p2810) ∨ (¬ p2747) ∨ (¬ p4619) ∨ (¬ p4500))
    : (¬ p2881) ∨ p2630 ∨ (¬ p2946) ∨ p2331 ∨ p2396 ∨ (¬ p2737) ∨ p2440 ∨ p2177 ∨ p2696 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2630) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4903 := (Or.elim h73820 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u11 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p4619 := (Or.elim h73672 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u14 : p2747 := (Or.elim h73302 (fun q0 => q0) (fun r0 => (False.elim (r0 u5))));
    let u15 : p4703 := (Or.elim h73714 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u16 : p4500 := (Or.elim h73602 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u17 : p4785 := (Or.elim h73758 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u18 : p4714 := (Or.elim h73720 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h66744 (fun q0 => (False.elim (q0 u17))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u18))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u15))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u14))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u13))) (fun r8 => (False.elim (r8 u16)))))))))))))))))))))

theorem step81805 (p2727 p2992 p3662 p4111 p4700 : Prop)
    (h73439 : (¬ p2992) ∨ (¬ p3662))
    (h73518 : p4111 ∨ p2727)
    (h27082 : p3662 ∨ (¬ p4111) ∨ (¬ p4700))
    : (¬ p2992) ∨ p2727 ∨ (¬ p4700) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3662) := (Or.elim h73439 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h27082 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u2)))))))

theorem step81807 (p2641 p2992 p3662 p4154 p4336 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73439 : (¬ p2992) ∨ (¬ p3662))
    (h32795 : p3662 ∨ (¬ p4154) ∨ (¬ p4336))
    : p2641 ∨ (¬ p2992) ∨ (¬ p4336) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p3662) := (Or.elim h73439 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h32795 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step81809 (p2881 p4042 p4903 : Prop)
    (h73820 : p4903 ∨ (¬ p2881))
    (h8090 : p4042 ∨ (¬ p4903))
    : p4042 ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4042) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4903 := (Or.elim h73820 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h8090 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step81812 (p2881 p4903 p4905 : Prop)
    (h73820 : p4903 ∨ (¬ p2881))
    (h8094 : (¬ p4903) ∨ p4905)
    : (¬ p2881) ∨ p4905 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4905) := (fun h => hn (Or.inr h));
    let u2 : p4903 := (Or.elim h73820 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h8094 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step81823 (p2132 p2138 p2241 p2619 p2641 p3146 p3323 p3692 p3694 p4330 p4736 : Prop)
    (h73450 : p3694 ∨ p2619)
    (h73214 : p2138 ∨ p2132)
    (h73448 : p3692 ∨ p3146)
    (h64097 : (¬ p2138) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p3323) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p4330) ∨ (¬ p4736))
    : p2619 ∨ (¬ p2641) ∨ (¬ p4330) ∨ (¬ p3323) ∨ (¬ p2241) ∨ p2132 ∨ p3146 ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3694 := (Or.elim h73450 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h64097 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step81824 (p2230 p2241 p2563 p2589 p3125 p3189 p3256 p3744 p3905 p4110 p4604 p4736 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h73284 : p2589 ∨ p2230)
    (h73516 : p4110 ∨ p2563)
    (h49376 : (¬ p2241) ∨ (¬ p2589) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3744) ∨ (¬ p3905) ∨ (¬ p4110) ∨ (¬ p4604) ∨ (¬ p4736))
    : (¬ p3189) ∨ p3125 ∨ p2230 ∨ (¬ p2241) ∨ (¬ p3256) ∨ (¬ p4604) ∨ (¬ p3905) ∨ p2563 ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h49376 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step81825 (p2132 p2138 p2177 p3093 p3146 p3309 p3609 p4340 p4359 p4736 p4905 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h73214 : p2138 ∨ p2132)
    (h50349 : (¬ p2138) ∨ (¬ p2177) ∨ (¬ p3093) ∨ (¬ p3146) ∨ (¬ p3309) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4736) ∨ (¬ p4905))
    : p3609 ∨ (¬ p3309) ∨ (¬ p4736) ∨ p2132 ∨ (¬ p3093) ∨ (¬ p4359) ∨ (¬ p4905) ∨ (¬ p3146) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50349 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step81826 (p2177 p2449 p2696 p3005 p3093 p3309 p3365 p3877 p3947 p4044 p4666 p4736 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73390 : p3365 ∨ p2696)
    (h73488 : p3877 ∨ p3005)
    (h59895 : (¬ p2177) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p3947) ∨ (¬ p4044) ∨ (¬ p4666) ∨ (¬ p4736))
    : p2449 ∨ (¬ p4044) ∨ p2696 ∨ p3005 ∨ (¬ p4736) ∨ (¬ p4666) ∨ (¬ p2177) ∨ (¬ p3093) ∨ (¬ p3309) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h59895 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step81828 (p2363 p2406 p2774 p2780 p2819 p2982 p3379 p4347 p4358 p4450 p4736 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73564 : p4358 ∨ p2819)
    (h73560 : p4347 ∨ p2363)
    (h63310 : (¬ p2406) ∨ (¬ p2780) ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4450) ∨ (¬ p4736))
    : p2774 ∨ (¬ p2406) ∨ (¬ p2982) ∨ (¬ p4736) ∨ p2819 ∨ p2363 ∨ (¬ p4450) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h63310 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step81832 (p2132 p2138 p2449 p2619 p2737 p2807 p2811 p3146 p3692 p3694 p3950 p4734 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73448 : p3692 ∨ p3146)
    (h73450 : p3694 ∨ p2619)
    (h72735 : p4734)
    (h64190 : (¬ p2138) ∨ (¬ p2449) ∨ (¬ p2737) ∨ (¬ p2807) ∨ (¬ p2811) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3950) ∨ (¬ p4734))
    : (¬ p2737) ∨ p2132 ∨ (¬ p2811) ∨ (¬ p2807) ∨ p3146 ∨ (¬ p3950) ∨ p2619 ∨ (¬ p2449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3694 := (Or.elim h73450 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p4734 := h72735;
    (Or.elim h64190 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u11)))))))))))))))))))

theorem step81833 (p2427 p2737 p2811 p2901 p2946 p4235 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h55180 : (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p4235))
    : (¬ p2901) ∨ (¬ p2811) ∨ p2427 ∨ (¬ p2737) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h55180 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step81836 (p2459 p2737 p2811 p3166 p3256 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h63792 : (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p4348))
    : (¬ p2811) ∨ (¬ p2737) ∨ (¬ p3256) ∨ p2459 ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2811 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63792 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step81838 (p2449 p2737 p2807 p2811 p3246 p3690 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h57120 : (¬ p2449) ∨ (¬ p2737) ∨ (¬ p2807) ∨ (¬ p2811) ∨ (¬ p3690))
    : (¬ p2449) ∨ p3246 ∨ (¬ p2811) ∨ (¬ p2807) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h57120 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step81839 (p2264 p2737 p2807 p2811 p2881 p3570 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h46216 : (¬ p2264) ∨ (¬ p2737) ∨ (¬ p2807) ∨ (¬ p2811) ∨ (¬ p3570))
    : (¬ p2264) ∨ p2881 ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46216 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step81842 (p2811 p2946 p3136 p4315 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h20425 : (¬ p2811) ∨ (¬ p2946) ∨ (¬ p4315))
    : (¬ p2811) ∨ (¬ p2946) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2811 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20425 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step81844 (p2331 p2797 p2811 p4195 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h21973 : (¬ p2331) ∨ (¬ p2811) ∨ (¬ p4195))
    : p2797 ∨ (¬ p2811) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h21973 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step81847 (p2331 p2373 p2406 p2598 p2668 p2737 p2811 p3055 p3238 p3880 p4030 p4134 p4734 : Prop)
    (h73350 : p3055 ∨ p2598)
    (h72735 : p4734)
    (h73374 : p3238 ∨ p2406)
    (h73490 : p3880 ∨ p2373)
    (h58720 : (¬ p2331) ∨ (¬ p2668) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3055) ∨ (¬ p3238) ∨ (¬ p3880) ∨ (¬ p4030) ∨ (¬ p4134) ∨ (¬ p4734))
    : (¬ p4030) ∨ (¬ p2668) ∨ (¬ p2811) ∨ (¬ p2331) ∨ (¬ p2737) ∨ (¬ p4134) ∨ p2598 ∨ p2406 ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4030 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u10 : p4734 := h72735;
    let u11 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h58720 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u10)))))))))))))))))))))

theorem step81848 (p2667 p2797 p2811 p3987 p4195 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h12502 : (¬ p2667) ∨ (¬ p2811) ∨ (¬ p3987) ∨ (¬ p4195))
    : (¬ p2811) ∨ p2797 ∨ (¬ p2667) ∨ (¬ p3987) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2811 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h12502 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81849 (p2295 p2651 p2727 p2797 p2811 p3568 p4111 p4195 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73532 : p4195 ∨ p2797)
    (h73518 : p4111 ∨ p2727)
    (h42688 : (¬ p2651) ∨ (¬ p2811) ∨ (¬ p3568) ∨ (¬ p4111) ∨ (¬ p4195))
    : (¬ p2811) ∨ p2295 ∨ p2797 ∨ (¬ p2651) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2811 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42688 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step81850 (p2685 p2807 p2811 p3572 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h5200 : (¬ p2807) ∨ (¬ p2811) ∨ (¬ p3572))
    : (¬ p2811) ∨ (¬ p2807) ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2811 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h5200 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u3)))))))

theorem step81852 (p2811 p3005 p3166 p3877 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h5737 : (¬ p2811) ∨ (¬ p3166) ∨ (¬ p3877))
    : (¬ p2811) ∨ (¬ p3166) ∨ p3005 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2811 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h5737 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step81855 (p2811 p3286 p3755 p4035 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h6003 : (¬ p2811) ∨ (¬ p3286) ∨ (¬ p4035))
    : (¬ p2811) ∨ (¬ p3286) ∨ p3755 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2811 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h6003 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step81858 (p2284 p2737 p2811 p2901 p2958 p3051 p4320 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h46572 : (¬ p2284) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p4320))
    : p2901 ∨ (¬ p3051) ∨ (¬ p2958) ∨ (¬ p2811) ∨ (¬ p2284) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h46572 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step81859 (p2630 p2651 p2810 p2811 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h3749 : (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2811))
    : (¬ p2811) ∨ (¬ p2651) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2811 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h3749 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u0)))))))

theorem step81861 (p2440 p2542 p2573 p2663 p2737 p2811 p3016 p3574 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73270 : p2542 ∨ p2440)
    (h47713 : (¬ p2542) ∨ (¬ p2573) ∨ (¬ p2663) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3574))
    : (¬ p2737) ∨ p3016 ∨ (¬ p2811) ∨ (¬ p2573) ∨ p2440 ∨ (¬ p2663) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47713 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step81862 (p2630 p2810 p2811 p3016 p3166 p3189 p3574 p4360 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73422 : p3574 ∨ p3016)
    (h73316 : p2810 ∨ p2630)
    (h55336 : (¬ p2810) ∨ (¬ p2811) ∨ (¬ p3166) ∨ (¬ p3574) ∨ (¬ p4360))
    : p3189 ∨ (¬ p3166) ∨ (¬ p2811) ∨ p3016 ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55336 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step81874 (p2274 p2295 p2331 p2737 p2811 p3097 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h46169 : (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3097))
    : (¬ p2811) ∨ (¬ p2737) ∨ (¬ p2295) ∨ p2274 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2811 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46169 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step81876 (p2437 p2440 p2542 p2663 p2737 p2811 p3389 p3742 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73452 : p3742 ∨ p2437)
    (h47497 : (¬ p2542) ∨ (¬ p2663) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3389) ∨ (¬ p3742))
    : (¬ p2811) ∨ (¬ p3389) ∨ p2440 ∨ (¬ p2737) ∨ p2437 ∨ (¬ p2663) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2811 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47497 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step81877 (p2241 p2247 p2811 p4790 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h52294 : (¬ p2247) ∨ (¬ p2811) ∨ p4790)
    : p4790 ∨ (¬ p2811) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4790) := (fun h => hn (Or.inl h));
    let u1 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52294 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u0 r1)))))))

theorem step81883 (p2331 p2493 p2499 p2553 p2588 p2598 p2668 p2737 p2811 p3055 p4030 p4405 p4734 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73350 : p3055 ∨ p2598)
    (h72735 : p4734)
    (h73282 : p2588 ∨ p2553)
    (h51331 : (¬ p2331) ∨ (¬ p2499) ∨ (¬ p2588) ∨ (¬ p2668) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3055) ∨ (¬ p4030) ∨ (¬ p4405) ∨ (¬ p4734))
    : (¬ p2737) ∨ (¬ p2668) ∨ (¬ p4405) ∨ p2493 ∨ (¬ p2331) ∨ p2598 ∨ (¬ p2811) ∨ p2553 ∨ (¬ p4030) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p4734 := h72735;
    let u12 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h51331 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (r8 u11)))))))))))))))))))))

theorem step81886 (p2493 p2499 p2573 p2663 p2811 p2839 p4257 p5052 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h64110 : (¬ p2499) ∨ (¬ p2573) ∨ (¬ p2663) ∨ (¬ p2811) ∨ (¬ p2839) ∨ (¬ p4257) ∨ (¬ p5052))
    : (¬ p2573) ∨ (¬ p2839) ∨ (¬ p2663) ∨ p2493 ∨ (¬ p5052) ∨ (¬ p4257) ∨ (¬ p2811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5052 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h64110 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step81889 (p2737 p2807 p2811 p3367 p3585 p4343 p4652 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h42044 : (¬ p2737) ∨ (¬ p2807) ∨ (¬ p2811) ∨ (¬ p3585) ∨ (¬ p4343) ∨ (¬ p4652))
    : (¬ p2737) ∨ (¬ p2811) ∨ p3367 ∨ (¬ p2807) ∨ (¬ p4652) ∨ (¬ p4343) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42044 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step81890 (p2331 p2737 p2811 p3367 p3585 p4343 p4975 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h41381 : (¬ p2331) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3585) ∨ (¬ p4343) ∨ (¬ p4975))
    : (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2331) ∨ (¬ p4343) ∨ p3367 ∨ (¬ p4975) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41381 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step81897 (p2761 p4381 p4831 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h48701 : (¬ p4381) ∨ p4831)
    : p2761 ∨ p4831 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4831) := (fun h => hn (Or.inr h));
    let u2 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48701 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step81898 (p2761 p2911 p3201 p3266 p3644 p3657 p3876 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73434 : p3644 ∨ p2911)
    (h73486 : p3876 ∨ p3201)
    (h48429 : (¬ p3266) ∨ (¬ p3644) ∨ (¬ p3657) ∨ (¬ p3876) ∨ (¬ p4381))
    : p2761 ∨ (¬ p3657) ∨ p2911 ∨ p3201 ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48429 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step81899 (p2132 p2138 p2761 p2870 p3246 p3690 p4244 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73214 : p2138 ∨ p2132)
    (h73540 : p4244 ∨ p2870)
    (h73446 : p3690 ∨ p3246)
    (h45430 : (¬ p2138) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4381))
    : p2761 ∨ p2132 ∨ p2870 ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45430 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81900 (p2396 p2761 p3192 p3276 p4107 p4381 p4712 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73514 : p4107 ∨ p2396)
    (h52300 : (¬ p3192) ∨ (¬ p3276) ∨ (¬ p4107) ∨ (¬ p4381) ∨ (¬ p4712))
    : p2761 ∨ (¬ p3276) ∨ p2396 ∨ (¬ p3192) ∨ (¬ p4712) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52300 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step81901 (p2417 p2761 p3363 p3367 p3389 p3540 p3585 p4278 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73546 : p4278 ∨ p2417)
    (h73402 : p3540 ∨ p3389)
    (h73428 : p3585 ∨ p3367)
    (h53940 : (¬ p3363) ∨ (¬ p3540) ∨ (¬ p3585) ∨ (¬ p4278) ∨ (¬ p4381))
    : p2761 ∨ p2417 ∨ (¬ p3363) ∨ p3389 ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h53940 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step81903 (p2417 p2598 p2761 p3055 p3201 p3876 p4278 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73546 : p4278 ∨ p2417)
    (h73486 : p3876 ∨ p3201)
    (h73350 : p3055 ∨ p2598)
    (h61478 : (¬ p3055) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4381))
    : p2761 ∨ p2417 ∨ p3201 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61478 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81904 (p2241 p2417 p2630 p2641 p2761 p2797 p3389 p3540 p4195 p4278 p4381 p5193 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73532 : p4195 ∨ p2797)
    (h73546 : p4278 ∨ p2417)
    (h73402 : p3540 ∨ p3389)
    (h51442 : (¬ p2241) ∨ (¬ p2630) ∨ (¬ p2641) ∨ (¬ p3540) ∨ (¬ p4195) ∨ (¬ p4278) ∨ (¬ p4381) ∨ (¬ p5193))
    : p2761 ∨ p2797 ∨ (¬ p2241) ∨ (¬ p2641) ∨ p2417 ∨ p3389 ∨ (¬ p5193) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h51442 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step81905 (p2417 p2761 p2911 p3266 p4278 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73546 : p4278 ∨ p2417)
    (h46196 : (¬ p2911) ∨ (¬ p3266) ∨ (¬ p4278) ∨ (¬ p4381))
    : p2761 ∨ (¬ p3266) ∨ (¬ p2911) ∨ p2417 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46196 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81906 (p2417 p2761 p3461 p4187 p4276 p4278 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73546 : p4278 ∨ p2417)
    (h41055 : (¬ p3461) ∨ (¬ p4187) ∨ (¬ p4276) ∨ (¬ p4278) ∨ (¬ p4381))
    : p2761 ∨ (¬ p3461) ∨ (¬ p4187) ∨ p2417 ∨ (¬ p4276) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41055 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step81907 (p2417 p2437 p2651 p2657 p2761 p3742 p4278 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73546 : p4278 ∨ p2417)
    (h73452 : p3742 ∨ p2437)
    (h73288 : p2657 ∨ p2651)
    (h44820 : (¬ p2657) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4381))
    : p2761 ∨ p2417 ∨ p2437 ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44820 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81908 (p2417 p2662 p2727 p2761 p3389 p3540 p4111 p4278 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73546 : p4278 ∨ p2417)
    (h73518 : p4111 ∨ p2727)
    (h73402 : p3540 ∨ p3389)
    (h43629 : (¬ p2662) ∨ (¬ p3540) ∨ (¬ p4111) ∨ (¬ p4278) ∨ (¬ p4381))
    : p2761 ∨ p2417 ∨ (¬ p2662) ∨ p2727 ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43629 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step81909 (p2417 p2440 p2542 p2662 p2761 p3389 p3540 p4278 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73546 : p4278 ∨ p2417)
    (h73402 : p3540 ∨ p3389)
    (h73270 : p2542 ∨ p2440)
    (h61776 : (¬ p2542) ∨ (¬ p2662) ∨ (¬ p3540) ∨ (¬ p4278) ∨ (¬ p4381))
    : p2761 ∨ p2417 ∨ p3389 ∨ p2440 ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61776 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step81910 (p2230 p2427 p2589 p2761 p3246 p3690 p4235 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73446 : p3690 ∨ p3246)
    (h73284 : p2589 ∨ p2230)
    (h73536 : p4235 ∨ p2427)
    (h43992 : (¬ p2589) ∨ (¬ p3690) ∨ (¬ p4235) ∨ (¬ p4381))
    : p2761 ∨ p3246 ∨ p2230 ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43992 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81912 (p2406 p2417 p2761 p3347 p3389 p3540 p4278 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73546 : p4278 ∨ p2417)
    (h73402 : p3540 ∨ p3389)
    (h54878 : (¬ p2406) ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p4278) ∨ (¬ p4381))
    : p2761 ∨ p2417 ∨ (¬ p3347) ∨ (¬ p2406) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54878 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step81913 (p2132 p2417 p2761 p2860 p3389 p3540 p3737 p4278 p4381 p4729 p5250 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73574 : p4381 ∨ p2761)
    (h73402 : p3540 ∨ p3389)
    (h58408 : (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3540) ∨ (¬ p3737) ∨ (¬ p4278) ∨ (¬ p4381) ∨ (¬ p4729) ∨ (¬ p5250))
    : p2417 ∨ p2761 ∨ (¬ p2860) ∨ (¬ p2132) ∨ (¬ p4729) ∨ (¬ p5250) ∨ (¬ p3737) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h58408 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step81916 (p2417 p2608 p2753 p2761 p2774 p3389 p3540 p3914 p4278 p4381 p5193 p5250 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73574 : p4381 ∨ p2761)
    (h73402 : p3540 ∨ p3389)
    (h50565 : (¬ p2608) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3540) ∨ (¬ p3914) ∨ (¬ p4278) ∨ (¬ p4381) ∨ (¬ p5193) ∨ (¬ p5250))
    : (¬ p3914) ∨ p2417 ∨ p2761 ∨ (¬ p2608) ∨ (¬ p5193) ∨ (¬ p2774) ∨ (¬ p2753) ∨ p3389 ∨ (¬ p5250) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3914 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h50565 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step81917 (p2417 p2761 p2922 p2928 p3379 p3452 p4278 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73546 : p4278 ∨ p2417)
    (h73394 : p3452 ∨ p3379)
    (h73320 : p2928 ∨ p2922)
    (h44191 : (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4278) ∨ (¬ p4381))
    : p2761 ∨ p2417 ∨ p3379 ∨ p2922 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44191 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81920 (p2717 p2761 p3266 p3516 p3821 p3959 p4381 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73574 : p4381 ∨ p2761)
    (h46080 : (¬ p2717) ∨ (¬ p3266) ∨ (¬ p3821) ∨ (¬ p3959) ∨ (¬ p4381))
    : p3516 ∨ p2761 ∨ (¬ p2717) ∨ (¬ p3266) ∨ (¬ p3959) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46080 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step81923 (p2417 p2761 p3506 p4278 p4381 p4653 p4661 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73546 : p4278 ∨ p2417)
    (h48368 : (¬ p3506) ∨ (¬ p4278) ∨ (¬ p4381) ∨ (¬ p4653) ∨ (¬ p4661))
    : p2761 ∨ (¬ p3506) ∨ p2417 ∨ (¬ p4661) ∨ (¬ p4653) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4653 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48368 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step81924 (p2528 p2761 p3266 p3657 p4381 p4438 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h41292 : (¬ p2528) ∨ (¬ p3266) ∨ (¬ p3657) ∨ (¬ p4381) ∨ (¬ p4438))
    : p2761 ∨ (¬ p3266) ∨ (¬ p4438) ∨ (¬ p3657) ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41292 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step81925 (p2363 p2761 p3266 p3657 p4381 p4503 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h41140 : (¬ p2363) ∨ (¬ p3266) ∨ (¬ p3657) ∨ (¬ p4381) ∨ (¬ p4503))
    : p2761 ∨ (¬ p3266) ∨ (¬ p3657) ∨ (¬ p4503) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41140 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step81926 (p2088 p2761 p3266 p3657 p4381 p4592 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h40941 : (¬ p2088) ∨ (¬ p3266) ∨ (¬ p3657) ∨ (¬ p4381) ∨ (¬ p4592))
    : p2761 ∨ (¬ p3266) ∨ (¬ p2088) ∨ (¬ p4592) ∨ (¬ p3657) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4592 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h40941 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step81927 (p2417 p2630 p2662 p2761 p2810 p3389 p3540 p4278 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73546 : p4278 ∨ p2417)
    (h73402 : p3540 ∨ p3389)
    (h73316 : p2810 ∨ p2630)
    (h56770 : (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3540) ∨ (¬ p4278) ∨ (¬ p4381))
    : p2761 ∨ p2417 ∨ p3389 ∨ p2630 ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56770 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step81928 (p2761 p3266 p4381 p4443 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h19928 : (¬ p3266) ∨ (¬ p4381) ∨ (¬ p4443))
    : p2761 ∨ (¬ p3266) ∨ (¬ p4443) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4443 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h19928 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step81930 (p2383 p2387 p2668 p2761 p2787 p3276 p3323 p3355 p3362 p4037 p4381 p4625 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73508 : p4037 ∨ p3323)
    (h73246 : p2387 ∨ p2383)
    (h57381 : (¬ p2387) ∨ (¬ p2668) ∨ (¬ p2787) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3362) ∨ (¬ p4037) ∨ (¬ p4381) ∨ (¬ p4625))
    : (¬ p3276) ∨ (¬ p2668) ∨ p2761 ∨ p3323 ∨ (¬ p3355) ∨ (¬ p4625) ∨ (¬ p3362) ∨ p2383 ∨ (¬ p2787) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h57381 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step81931 (p2417 p2696 p2761 p2797 p3389 p3540 p4228 p4278 p4381 p4729 p5250 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73402 : p3540 ∨ p3389)
    (h73546 : p4278 ∨ p2417)
    (h61649 : (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3540) ∨ (¬ p4228) ∨ (¬ p4278) ∨ (¬ p4381) ∨ (¬ p4729) ∨ (¬ p5250))
    : (¬ p4228) ∨ p2761 ∨ p3389 ∨ (¬ p4729) ∨ (¬ p2696) ∨ p2417 ∨ (¬ p2797) ∨ (¬ p5250) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4228 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h61649 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step81932 (p2246 p2651 p2744 p2761 p3016 p3266 p3366 p3516 p3564 p3820 p3821 p4330 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73470 : p3821 ∨ p3516)
    (h64140 : (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3016) ∨ (¬ p3266) ∨ (¬ p3366) ∨ (¬ p3564) ∨ (¬ p3820) ∨ (¬ p3821) ∨ (¬ p4330) ∨ (¬ p4381))
    : (¬ p3266) ∨ (¬ p3820) ∨ (¬ p3564) ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p2246) ∨ (¬ p4330) ∨ p2761 ∨ (¬ p3016) ∨ p3516 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3820 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h64140 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (False.elim (r9 u11)))))))))))))))))))))))

theorem step81933 (p2417 p2761 p3366 p3367 p3425 p4106 p4278 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73546 : p4278 ∨ p2417)
    (h45335 : (¬ p3366) ∨ (¬ p3367) ∨ (¬ p3425) ∨ (¬ p4106) ∨ (¬ p4278) ∨ (¬ p4381))
    : p2761 ∨ p2417 ∨ (¬ p3367) ∨ (¬ p4106) ∨ (¬ p3366) ∨ (¬ p3425) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4106 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45335 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step81934 (p2396 p2553 p2573 p2579 p2588 p2761 p4107 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73514 : p4107 ∨ p2396)
    (h73282 : p2588 ∨ p2553)
    (h73274 : p2579 ∨ p2573)
    (h46058 : (¬ p2579) ∨ (¬ p2588) ∨ (¬ p4107) ∨ (¬ p4381))
    : p2761 ∨ p2396 ∨ p2553 ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46058 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81935 (p2230 p2761 p3246 p3389 p3540 p3690 p4001 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73446 : p3690 ∨ p3246)
    (h73402 : p3540 ∨ p3389)
    (h62284 : (¬ p2230) ∨ (¬ p3540) ∨ (¬ p3690) ∨ (¬ p4001) ∨ (¬ p4381))
    : p2761 ∨ p3246 ∨ p3389 ∨ (¬ p2230) ∨ (¬ p4001) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h62284 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step81937 (p2295 p2331 p2396 p2761 p2963 p3568 p4107 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73338 : p2963 ∨ p2331)
    (h73416 : p3568 ∨ p2295)
    (h73514 : p4107 ∨ p2396)
    (h45320 : (¬ p2963) ∨ (¬ p3568) ∨ (¬ p4107) ∨ (¬ p4381))
    : p2761 ∨ p2331 ∨ p2295 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45320 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81939 (p2761 p2901 p2946 p2952 p3246 p3690 p4320 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73330 : p2952 ∨ p2946)
    (h73552 : p4320 ∨ p2901)
    (h73446 : p3690 ∨ p3246)
    (h63296 : (¬ p2952) ∨ (¬ p3690) ∨ (¬ p4320) ∨ (¬ p4381))
    : p2761 ∨ p2946 ∨ p2901 ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63296 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81941 (p2298 p2331 p2396 p2761 p2807 p3414 p4107 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73392 : p3414 ∨ p2807)
    (h73514 : p4107 ∨ p2396)
    (h43918 : (¬ p2298) ∨ (¬ p2331) ∨ (¬ p3414) ∨ (¬ p4107) ∨ (¬ p4381))
    : p2761 ∨ (¬ p2298) ∨ p2807 ∨ (¬ p2331) ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p2298 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43918 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step81943 (p2573 p2761 p3461 p3564 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h64977 : (¬ p2573) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p4381))
    : p2761 ∨ (¬ p3461) ∨ (¬ p2573) ∨ (¬ p3564) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h64977 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81947 (p2761 p4822 p4826 : Prop)
    (h73778 : p4822 ∨ p2761)
    (h7904 : (¬ p4822) ∨ p4826)
    : p2761 ∨ p4826 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4826) := (fun h => hn (Or.inr h));
    let u2 : p4822 := (Or.elim h73778 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7904 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step81948 (p2641 p2996 p4067 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h28364 : p2996 ∨ (¬ p4067) ∨ (¬ p4154))
    : p2641 ∨ (¬ p4067) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h28364 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step81950 (p2992 p2996 p3662 p4386 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h25522 : p2996 ∨ (¬ p3662) ∨ (¬ p4386))
    : p2992 ∨ (¬ p4386) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h25522 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step81952 (p2727 p2996 p4111 p4112 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h26519 : p2996 ∨ (¬ p4111) ∨ (¬ p4112))
    : p2996 ∨ (¬ p4112) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : p4112 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h26519 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step81953 (p2996 p3189 p4044 p4360 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h6638 : p2996 ∨ (¬ p4044) ∨ (¬ p4360))
    : p3189 ∨ (¬ p4044) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h6638 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step81961 (p2641 p2996 p3027 p3323 p3552 p4037 p4154 p4620 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73340 : p3027 ∨ p2996)
    (h73508 : p4037 ∨ p3323)
    (h54080 : (¬ p3027) ∨ (¬ p3552) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4620))
    : p2641 ∨ (¬ p3552) ∨ (¬ p4620) ∨ p2996 ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p3552 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54080 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step81963 (p2177 p2241 p2299 p2449 p2553 p2573 p2579 p2588 p2996 p3027 p4668 p5193 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73274 : p2579 ∨ p2573)
    (h73234 : p2299 ∨ p2177)
    (h73282 : p2588 ∨ p2553)
    (h63900 : (¬ p2241) ∨ (¬ p2299) ∨ (¬ p2449) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3027) ∨ (¬ p4668) ∨ (¬ p5193))
    : p2996 ∨ (¬ p2449) ∨ p2573 ∨ (¬ p5193) ∨ (¬ p4668) ∨ (¬ p2241) ∨ p2177 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h63900 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step81965 (p2881 p2996 p3027 p3189 p4280 p4360 p4548 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73566 : p4360 ∨ p3189)
    (h51723 : (¬ p2881) ∨ (¬ p3027) ∨ (¬ p4280) ∨ (¬ p4360) ∨ (¬ p4548))
    : p2996 ∨ p3189 ∨ (¬ p4548) ∨ (¬ p2881) ∨ (¬ p4280) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4280 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h51723 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step81968 (p2264 p2459 p2992 p2996 p3027 p3662 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73440 : p3662 ∨ p2992)
    (h63716 : (¬ p2264) ∨ (¬ p2459) ∨ (¬ p3027) ∨ (¬ p3662))
    : p2996 ∨ p2992 ∨ (¬ p2264) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h63716 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step81972 (p2177 p2996 p3027 p3189 p4360 p4548 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73566 : p4360 ∨ p3189)
    (h71523 : (¬ p4360) ∨ (¬ p4548) ∨ (¬ p2177) ∨ (¬ p3027))
    : p2996 ∨ p3189 ∨ (¬ p2177) ∨ (¬ p4548) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71523 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81973 (p2177 p2996 p3027 p3189 p4360 p4548 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73566 : p4360 ∨ p3189)
    (h71524 : (¬ p4360) ∨ (¬ p4548) ∨ (¬ p3027) ∨ (¬ p2177))
    : p2996 ∨ p3189 ∨ (¬ p4548) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71524 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step81975 (p2553 p2588 p2651 p2727 p2996 p3027 p3552 p4111 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73340 : p3027 ∨ p2996)
    (h73518 : p4111 ∨ p2727)
    (h43870 : (¬ p2588) ∨ (¬ p2651) ∨ (¬ p3027) ∨ (¬ p3552) ∨ (¬ p4111))
    : (¬ p3552) ∨ p2553 ∨ p2996 ∨ (¬ p2651) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3552 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43870 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step81977 (p2264 p2651 p2727 p2996 p3027 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73340 : p3027 ∨ p2996)
    (h43145 : (¬ p2264) ∨ (¬ p2651) ∨ (¬ p3027) ∨ (¬ p4111))
    : p2727 ∨ (¬ p2651) ∨ (¬ p2264) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43145 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81978 (p2331 p2641 p2946 p2952 p2996 p3027 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73340 : p3027 ∨ p2996)
    (h73330 : p2952 ∨ p2946)
    (h43657 : (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3027) ∨ (¬ p4154))
    : p2641 ∨ p2996 ∨ p2946 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43657 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step81980 (p2641 p2651 p2807 p2996 p3027 p3414 p4154 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73526 : p4154 ∨ p2641)
    (h73392 : p3414 ∨ p2807)
    (h44169 : (¬ p2651) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p4154))
    : p2996 ∨ p2641 ∨ (¬ p2651) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44169 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step81996 (p2241 p2254 p2807 p2996 p3027 p3414 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73392 : p3414 ∨ p2807)
    (h40952 : (¬ p2241) ∨ (¬ p2254) ∨ (¬ p3027) ∨ (¬ p3414))
    : p2996 ∨ (¬ p2241) ∨ (¬ p2254) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h40952 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step81997 (p2440 p2727 p2807 p2996 p3027 p3414 p4111 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73518 : p4111 ∨ p2727)
    (h73392 : p3414 ∨ p2807)
    (h43568 : (¬ p2440) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p4111))
    : p2996 ∨ p2727 ∨ (¬ p2440) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43568 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step81998 (p2630 p2727 p2807 p2996 p3027 p3414 p4111 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73518 : p4111 ∨ p2727)
    (h73392 : p3414 ∨ p2807)
    (h71525 : (¬ p3027) ∨ (¬ p4111) ∨ (¬ p2630) ∨ (¬ p3414))
    : p2996 ∨ p2727 ∨ (¬ p2630) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71525 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step82001 (p2727 p2807 p2946 p2996 p3027 p3414 p4111 p4704 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73518 : p4111 ∨ p2727)
    (h73392 : p3414 ∨ p2807)
    (h73046 : p4704)
    (h48129 : (¬ p2946) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p4111) ∨ (¬ p4704))
    : p2996 ∨ p2727 ∨ p2807 ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4704 := h73046;
    (Or.elim h48129 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step82003 (p2241 p2254 p2996 p3027 p3166 p3172 p4044 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h73340 : p3027 ∨ p2996)
    (h41239 : (¬ p2241) ∨ (¬ p2254) ∨ (¬ p3027) ∨ (¬ p3172) ∨ (¬ p4044))
    : (¬ p4044) ∨ p3166 ∨ (¬ p2241) ∨ p2996 ∨ (¬ p2254) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4044 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41239 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step82004 (p2245 p2608 p2744 p2807 p2996 p3027 p3414 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73392 : p3414 ∨ p2807)
    (h52662 : (¬ p2245) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3027) ∨ (¬ p3414))
    : p2996 ∨ (¬ p2608) ∨ p2807 ∨ (¬ p2245) ∨ (¬ p2744) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52662 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step82007 (p2245 p2749 p2807 p2996 p3027 p3379 p3414 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73392 : p3414 ∨ p2807)
    (h71527 : (¬ p3414) ∨ (¬ p3379) ∨ (¬ p3027) ∨ (¬ p2749) ∨ (¬ p2245))
    : p2996 ∨ (¬ p2245) ∨ p2807 ∨ (¬ p3379) ∨ (¬ p2749) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h71527 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step82008 (p2264 p2417 p2696 p2742 p2996 p3027 p3363 p3367 p3389 p3540 p3585 p4278 p4666 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73340 : p3027 ∨ p2996)
    (h73402 : p3540 ∨ p3389)
    (h73428 : p3585 ∨ p3367)
    (h71528 : (¬ p2742) ∨ (¬ p3585) ∨ (¬ p3363) ∨ (¬ p4278) ∨ (¬ p2696) ∨ (¬ p2264) ∨ (¬ p3027) ∨ (¬ p3540) ∨ (¬ p4666))
    : p2417 ∨ p2996 ∨ (¬ p4666) ∨ (¬ p2264) ∨ (¬ p3363) ∨ (¬ p2696) ∨ p3389 ∨ p3367 ∨ (¬ p2742) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h71528 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step82009 (p2241 p2449 p2996 p3027 p3631 p3817 : Prop)
    (h73468 : p3817 ∨ p3631)
    (h73340 : p3027 ∨ p2996)
    (h42964 : (¬ p2241) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3817))
    : p3631 ∨ p2996 ∨ (¬ p2449) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42964 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step82011 (p2264 p2459 p2727 p2996 p3027 p4111 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73518 : p4111 ∨ p2727)
    (h55691 : (¬ p2264) ∨ (¬ p2459) ∨ (¬ p3027) ∨ (¬ p4111))
    : p2996 ∨ (¬ p2264) ∨ (¬ p2459) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55691 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step82012 (p2241 p2264 p2459 p2996 p3027 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h43123 : (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p3027))
    : p2996 ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h43123 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step82013 (p2177 p2253 p2651 p2727 p2881 p2996 p3027 p3051 p3556 p3570 p4111 p4524 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73518 : p4111 ∨ p2727)
    (h73418 : p3570 ∨ p2881)
    (h72962 : p4524)
    (h73414 : p3556 ∨ p3051)
    (h71529 : (¬ p3027) ∨ (¬ p4111) ∨ (¬ p2177) ∨ (¬ p3556) ∨ (¬ p2651) ∨ (¬ p2253) ∨ (¬ p4524) ∨ (¬ p3570))
    : p2996 ∨ p2727 ∨ p2881 ∨ (¬ p2177) ∨ (¬ p2651) ∨ (¬ p2253) ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4524 := h72962;
    let u11 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h71529 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u9)))))))))))))))))

theorem step82017 (p2630 p2651 p2807 p2810 p2996 p3027 p3414 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73316 : p2810 ∨ p2630)
    (h73392 : p3414 ∨ p2807)
    (h42741 : (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3027) ∨ (¬ p3414))
    : p2996 ∨ (¬ p2651) ∨ p2630 ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42741 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step82018 (p2230 p2584 p2589 p2641 p2667 p2996 p3027 p3579 p4154 p4646 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73526 : p4154 ∨ p2641)
    (h73284 : p2589 ∨ p2230)
    (h41208 : (¬ p2584) ∨ (¬ p2589) ∨ (¬ p2667) ∨ (¬ p3027) ∨ (¬ p3579) ∨ (¬ p4154) ∨ (¬ p4646))
    : p2996 ∨ p2641 ∨ p2230 ∨ (¬ p3579) ∨ (¬ p2584) ∨ (¬ p4646) ∨ (¬ p2667) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41208 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step82022 (p2727 p2996 p3016 p3027 p3574 p3579 p4111 p4711 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73518 : p4111 ∨ p2727)
    (h73422 : p3574 ∨ p3016)
    (h40932 : (¬ p3027) ∨ (¬ p3574) ∨ (¬ p3579) ∨ (¬ p4111) ∨ (¬ p4711))
    : p2996 ∨ p2727 ∨ (¬ p4711) ∨ (¬ p3579) ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4711 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h40932 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step82024 (p2659 p2727 p2996 p3027 p3389 p3540 p3579 p4111 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73518 : p4111 ∨ p2727)
    (h73402 : p3540 ∨ p3389)
    (h50652 : (¬ p2659) ∨ (¬ p3027) ∨ (¬ p3540) ∨ (¬ p3579) ∨ (¬ p4111))
    : p2996 ∨ p2727 ∨ p3389 ∨ (¬ p3579) ∨ (¬ p2659) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50652 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step82026 (p2331 p2727 p2807 p2996 p3027 p3414 p4111 p4975 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73340 : p3027 ∨ p2996)
    (h73392 : p3414 ∨ p2807)
    (h60447 : (¬ p2331) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p4111) ∨ (¬ p4975))
    : p2727 ∨ p2996 ∨ (¬ p2331) ∨ p2807 ∨ (¬ p4975) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60447 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step82028 (p2230 p2406 p2440 p2542 p2589 p2655 p2727 p2996 p3027 p3238 p4809 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73770 : p4809 ∨ p2727)
    (h73374 : p3238 ∨ p2406)
    (h73284 : p2589 ∨ p2230)
    (h73270 : p2542 ∨ p2440)
    (h66832 : (¬ p3027) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3238) ∨ (¬ p4809) ∨ (¬ p2655))
    : p2996 ∨ p2727 ∨ p2406 ∨ (¬ p2655) ∨ p2230 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4809 := (Or.elim h73770 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h66832 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step82029 (p2406 p2440 p2542 p2807 p2996 p3027 p3238 p3402 p3414 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73392 : p3414 ∨ p2807)
    (h73270 : p2542 ∨ p2440)
    (h73374 : p3238 ∨ p2406)
    (h44034 : (¬ p2542) ∨ (¬ p3027) ∨ (¬ p3238) ∨ (¬ p3402) ∨ (¬ p3414))
    : (¬ p3402) ∨ p2996 ∨ p2807 ∨ p2440 ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3402 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h44034 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step82030 (p2177 p2299 p2911 p2992 p2996 p3027 p3662 p4066 p4279 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73234 : p2299 ∨ p2177)
    (h73340 : p3027 ∨ p2996)
    (h46291 : (¬ p2299) ∨ (¬ p2911) ∨ (¬ p3027) ∨ (¬ p3662) ∨ (¬ p4066) ∨ (¬ p4279))
    : p2992 ∨ (¬ p4066) ∨ (¬ p2911) ∨ p2177 ∨ (¬ p4279) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4279 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h46291 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step82037 (p2241 p2449 p2761 p2996 p3027 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h43090 : (¬ p2241) ∨ (¬ p2449) ∨ (¬ p2761) ∨ (¬ p3027))
    : p2996 ∨ (¬ p2449) ∨ (¬ p2761) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h43090 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step82039 (p2341 p2996 p3027 p3189 p4360 p4548 p4854 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73566 : p4360 ∨ p3189)
    (h41077 : (¬ p2341) ∨ (¬ p3027) ∨ (¬ p4360) ∨ (¬ p4548) ∨ (¬ p4854))
    : p2996 ∨ p3189 ∨ (¬ p4548) ∨ (¬ p2341) ∨ (¬ p4854) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4854 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41077 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step82041 (p2761 p2807 p2996 p3027 p3286 p3414 p4660 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73392 : p3414 ∨ p2807)
    (h44062 : (¬ p2761) ∨ (¬ p3027) ∨ (¬ p3286) ∨ (¬ p3414) ∨ (¬ p4660))
    : (¬ p3286) ∨ p2996 ∨ (¬ p4660) ∨ p2807 ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3286 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44062 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step82042 (p2241 p2264 p2996 p3027 p4416 p4592 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h53061 : (¬ p2241) ∨ (¬ p2264) ∨ (¬ p3027) ∨ (¬ p4416) ∨ (¬ p4592))
    : p2996 ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p4592) ∨ (¬ p4416) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4592 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4416 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h53061 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step82044 (p2253 p2331 p2641 p2717 p2881 p2996 p3027 p3425 p3659 p4154 p4280 p4736 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h73340 : p3027 ∨ p2996)
    (h73526 : p4154 ∨ p2641)
    (h50876 : (¬ p2253) ∨ (¬ p2331) ∨ (¬ p2881) ∨ (¬ p3027) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4154) ∨ (¬ p4280) ∨ (¬ p4736))
    : p2717 ∨ p2996 ∨ (¬ p2881) ∨ (¬ p3425) ∨ (¬ p2331) ∨ p2641 ∨ (¬ p4736) ∨ (¬ p4280) ∨ (¬ p2253) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4280 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h50876 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step82047 (p2220 p2241 p2373 p2449 p2982 p2996 p3027 p3951 p4120 p4524 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h72962 : p4524)
    (h73340 : p3027 ∨ p2996)
    (h73522 : p4120 ∨ p2220)
    (h51813 : (¬ p2241) ∨ (¬ p2373) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3951) ∨ (¬ p4120) ∨ (¬ p4524) ∨ (¬ p4948))
    : (¬ p2449) ∨ p2982 ∨ (¬ p2241) ∨ p2996 ∨ p2220 ∨ (¬ p2373) ∨ (¬ p3951) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4524 := h72962;
    let u9 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51813 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step82049 (p2245 p2807 p2996 p3027 p3189 p3256 p3414 p4118 p4360 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73566 : p4360 ∨ p3189)
    (h73392 : p3414 ∨ p2807)
    (h73520 : p4118 ∨ p3256)
    (h59244 : (¬ p2245) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p4118) ∨ (¬ p4360))
    : p2996 ∨ p3189 ∨ p2807 ∨ p3256 ∨ (¬ p2245) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h59244 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step82051 (p2449 p2761 p2992 p2996 p3027 p3662 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73440 : p3662 ∨ p2992)
    (h44401 : (¬ p2449) ∨ (¬ p2761) ∨ (¬ p3027) ∨ (¬ p3662))
    : p2996 ∨ p2992 ∨ (¬ p2761) ∨ (¬ p2449) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h44401 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step82052 (p2651 p2657 p2946 p2992 p2996 p3027 p3662 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73340 : p3027 ∨ p2996)
    (h73288 : p2657 ∨ p2651)
    (h42870 : (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3027) ∨ (¬ p3662))
    : p2992 ∨ p2996 ∨ p2651 ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42870 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step82053 (p2449 p2651 p2727 p2996 p3027 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73340 : p3027 ∨ p2996)
    (h43649 : (¬ p2449) ∨ (¬ p2651) ∨ (¬ p3027) ∨ (¬ p4111))
    : p2727 ∨ (¬ p2449) ∨ p2996 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43649 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step82056 (p2230 p2241 p2264 p2427 p2589 p2996 p3027 p3246 p3690 p4235 p4666 p5193 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73340 : p3027 ∨ p2996)
    (h73536 : p4235 ∨ p2427)
    (h73284 : p2589 ∨ p2230)
    (h50280 : (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2589) ∨ (¬ p3027) ∨ (¬ p3690) ∨ (¬ p4235) ∨ (¬ p4666) ∨ (¬ p5193))
    : (¬ p2264) ∨ p3246 ∨ p2996 ∨ p2427 ∨ p2230 ∨ (¬ p5193) ∨ (¬ p2241) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50280 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step82057 (p2727 p2807 p2996 p3027 p3414 p3425 p3471 p4111 p4236 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73392 : p3414 ∨ p2807)
    (h73396 : p3471 ∨ p3425)
    (h73340 : p3027 ∨ p2996)
    (h51998 : (¬ p3027) ∨ (¬ p3414) ∨ (¬ p3471) ∨ (¬ p4111) ∨ (¬ p4236))
    : p2727 ∨ (¬ p4236) ∨ p2807 ∨ p3425 ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51998 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step82059 (p2132 p2187 p2245 p2807 p2860 p2996 p3027 p3189 p3414 p4360 p4733 p4774 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73392 : p3414 ∨ p2807)
    (h73566 : p4360 ∨ p3189)
    (h55986 : (¬ p2132) ∨ (¬ p2187) ∨ (¬ p2245) ∨ (¬ p2860) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p4360) ∨ (¬ p4733) ∨ (¬ p4774))
    : p2996 ∨ p2807 ∨ p3189 ∨ (¬ p4733) ∨ (¬ p2132) ∨ (¬ p4774) ∨ (¬ p2860) ∨ (¬ p2187) ∨ (¬ p2245) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2807) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h55986 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step82061 (p2241 p2449 p2996 p3027 p3246 p3690 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73446 : p3690 ∨ p3246)
    (h43301 : (¬ p2241) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3690))
    : (¬ p2449) ∨ p2996 ∨ p3246 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43301 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step82062 (p2241 p2264 p2363 p2470 p2476 p2528 p2534 p2996 p3027 p4503 p5193 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73250 : p2476 ∨ p2470)
    (h73340 : p3027 ∨ p2996)
    (h63886 : (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2363) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3027) ∨ (¬ p4503) ∨ (¬ p5193))
    : p2528 ∨ p2470 ∨ (¬ p2264) ∨ (¬ p4503) ∨ (¬ p2241) ∨ p2996 ∨ (¬ p2363) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2470) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h63886 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step82063 (p2230 p2241 p2427 p2449 p2589 p2881 p2996 p3027 p3570 p4235 p4668 p5193 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73284 : p2589 ∨ p2230)
    (h73418 : p3570 ∨ p2881)
    (h73340 : p3027 ∨ p2996)
    (h49752 : (¬ p2241) ∨ (¬ p2449) ∨ (¬ p2589) ∨ (¬ p3027) ∨ (¬ p3570) ∨ (¬ p4235) ∨ (¬ p4668) ∨ (¬ p5193))
    : (¬ p2449) ∨ p2427 ∨ (¬ p5193) ∨ (¬ p4668) ∨ (¬ p2241) ∨ p2230 ∨ p2881 ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h49752 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step82064 (p2249 p2509 p2651 p2657 p2761 p2996 p3027 p3487 p3516 p4066 p4149 p4286 p5123 : Prop)
    (h73548 : p4286 ∨ p4149)
    (h73340 : p3027 ∨ p2996)
    (h73288 : p2657 ∨ p2651)
    (h57553 : (¬ p2249) ∨ (¬ p2509) ∨ (¬ p2657) ∨ (¬ p2761) ∨ (¬ p3027) ∨ (¬ p3487) ∨ (¬ p3516) ∨ (¬ p4066) ∨ (¬ p4286) ∨ (¬ p5123))
    : p4149 ∨ p2996 ∨ (¬ p4066) ∨ (¬ p3516) ∨ (¬ p2509) ∨ (¬ p3487) ∨ (¬ p2249) ∨ (¬ p2761) ∨ (¬ p5123) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4149) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4286 := (Or.elim h73548 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h57553 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step82065 (p2156 p2241 p2996 p3027 p3125 p3461 p3646 p3744 p3931 p4191 p4524 p4826 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h72962 : p4524)
    (h73530 : p4191 ∨ p3461)
    (h73436 : p3646 ∨ p2156)
    (h73340 : p3027 ∨ p2996)
    (h63922 : (¬ p2241) ∨ (¬ p3027) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p3931) ∨ (¬ p4191) ∨ (¬ p4524) ∨ (¬ p4826))
    : (¬ p3931) ∨ p3125 ∨ (¬ p4826) ∨ p3461 ∨ p2156 ∨ (¬ p2241) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3931 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4524 := h72962;
    let u9 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h63922 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step82068 (p2156 p2241 p2264 p2274 p2396 p2996 p3027 p3097 p3646 p4107 p4524 p4666 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73340 : p3027 ∨ p2996)
    (h73436 : p3646 ∨ p2156)
    (h73352 : p3097 ∨ p2274)
    (h72962 : p4524)
    (h63973 : (¬ p2241) ∨ (¬ p2264) ∨ (¬ p3027) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4107) ∨ (¬ p4524) ∨ (¬ p4666))
    : p2396 ∨ (¬ p2264) ∨ (¬ p2241) ∨ p2996 ∨ p2156 ∨ p2274 ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2396) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p4524 := h72962;
    (Or.elim h63973 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step82077 (p2177 p2996 p3027 p3177 p3189 p3960 p4360 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73566 : p4360 ∨ p3189)
    (h71531 : (¬ p2177) ∨ (¬ p3177) ∨ (¬ p3027) ∨ (¬ p3960) ∨ (¬ p4360))
    : (¬ p3960) ∨ p2996 ∨ (¬ p3177) ∨ p3189 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3960 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71531 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step82078 (p2187 p2192 p2249 p2459 p2946 p2952 p2996 p3027 p3256 p3989 p4044 p4173 p4282 p4348 p4503 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73502 : p3989 ∨ p2187)
    (h73340 : p3027 ∨ p2996)
    (h73528 : p4173 ∨ p2192)
    (h73562 : p4348 ∨ p2459)
    (h64725 : (¬ p2249) ∨ (¬ p2952) ∨ (¬ p3027) ∨ (¬ p3256) ∨ (¬ p3989) ∨ (¬ p4044) ∨ (¬ p4173) ∨ (¬ p4282) ∨ (¬ p4348) ∨ (¬ p4503))
    : (¬ p4282) ∨ (¬ p2249) ∨ (¬ p4044) ∨ p2946 ∨ p2187 ∨ (¬ p3256) ∨ p2996 ∨ (¬ p4503) ∨ p2192 ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4282 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u14 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h64725 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u14))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step82079 (p2166 p2191 p2210 p2241 p2651 p2657 p2996 p3027 p3166 p3172 p4652 : Prop)
    (h73355 : (¬ p3166) ∨ (¬ p3172))
    (h73288 : p2657 ∨ p2651)
    (h73340 : p3027 ∨ p2996)
    (h73221 : (¬ p2166) ∨ (¬ p2191))
    (h66828 : (¬ p2657) ∨ (¬ p3027) ∨ (¬ p4652) ∨ (¬ p2241) ∨ p2210 ∨ p3172 ∨ p2191)
    : (¬ p3166) ∨ p2210 ∨ (¬ p4652) ∨ p2651 ∨ p2996 ∨ (¬ p2241) ∨ (¬ p2166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p3172) := (Or.elim h73355 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u8 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : (¬ p2191) := (Or.elim h73221 (fun q0 => (False.elim (q0 u6))) (fun r0 => r0));
    (Or.elim h66828 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u1 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (False.elim (u10 r5)))))))))))))))

theorem step82081 (p2241 p2761 p2996 p3027 p3506 p4381 p4661 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73340 : p3027 ∨ p2996)
    (h43111 : (¬ p2241) ∨ (¬ p3027) ∨ (¬ p3506) ∨ (¬ p4381) ∨ (¬ p4661))
    : (¬ p4661) ∨ p2761 ∨ p2996 ∨ (¬ p3506) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4661 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43111 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step82082 (p2264 p2727 p2911 p2996 p3027 p3644 p4111 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73518 : p4111 ∨ p2727)
    (h73340 : p3027 ∨ p2996)
    (h58487 : (¬ p2264) ∨ (¬ p3027) ∨ (¬ p3644) ∨ (¬ p4111))
    : p2911 ∨ (¬ p2264) ∨ p2727 ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h58487 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step82084 (p2187 p2230 p2241 p2264 p2563 p2589 p2996 p3027 p3989 p4110 p4503 p5193 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73516 : p4110 ∨ p2563)
    (h73284 : p2589 ∨ p2230)
    (h73502 : p3989 ∨ p2187)
    (h54135 : (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2589) ∨ (¬ p3027) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4503) ∨ (¬ p5193))
    : p2996 ∨ (¬ p2241) ∨ (¬ p4503) ∨ p2563 ∨ (¬ p2264) ∨ (¬ p5193) ∨ p2230 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h54135 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step82085 (p2230 p2241 p2264 p2274 p2563 p2589 p2996 p3027 p3097 p3941 p4110 p5193 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73340 : p3027 ∨ p2996)
    (h73516 : p4110 ∨ p2563)
    (h73284 : p2589 ∨ p2230)
    (h51410 : (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2589) ∨ (¬ p3027) ∨ (¬ p3097) ∨ (¬ p3941) ∨ (¬ p4110) ∨ (¬ p5193))
    : (¬ p3941) ∨ p2274 ∨ (¬ p5193) ∨ (¬ p2264) ∨ p2996 ∨ (¬ p2241) ∨ p2563 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3941 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h51410 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step82087 (p2253 p2264 p2331 p2641 p2996 p3027 p4154 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73526 : p4154 ∨ p2641)
    (h43082 : (¬ p2253) ∨ (¬ p2264) ∨ (¬ p2331) ∨ (¬ p3027) ∨ (¬ p4154))
    : p2996 ∨ (¬ p2253) ∨ (¬ p2331) ∨ (¬ p2264) ∨ p2641 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43082 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step82088 (p2331 p2449 p2641 p2996 p3027 p4154 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73526 : p4154 ∨ p2641)
    (h56619 : (¬ p2331) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p4154))
    : p2996 ∨ p2641 ∨ (¬ p2331) ∨ (¬ p2449) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h56619 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step82092 (p2396 p2696 p2742 p2996 p3027 p3276 p3367 p3552 p3585 p3670 p4641 p5158 p5387 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h73428 : p3585 ∨ p3367)
    (h73340 : p3027 ∨ p2996)
    (h71532 : (¬ p5387) ∨ (¬ p3585) ∨ (¬ p2742) ∨ (¬ p2396) ∨ (¬ p3027) ∨ (¬ p2696) ∨ (¬ p5158) ∨ (¬ p3552) ∨ (¬ p4641) ∨ (¬ p3276))
    : p3670 ∨ (¬ p3552) ∨ p3367 ∨ (¬ p3276) ∨ (¬ p2742) ∨ p2996 ∨ (¬ p5158) ∨ (¬ p2396) ∨ (¬ p4641) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : p3552 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5158 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h71532 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step82093 (p2252 p2563 p2946 p2952 p2996 p3027 p3879 p4110 p4333 p4558 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73516 : p4110 ∨ p2563)
    (h73340 : p3027 ∨ p2996)
    (h51098 : (¬ p2252) ∨ (¬ p2952) ∨ (¬ p3027) ∨ (¬ p3879) ∨ (¬ p4110) ∨ (¬ p4333) ∨ (¬ p4558))
    : p2946 ∨ (¬ p2252) ∨ (¬ p3879) ∨ p2563 ∨ (¬ p4558) ∨ (¬ p4333) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h51098 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step82100 (p2249 p2493 p2499 p2651 p2657 p2761 p2996 p3027 p3487 p3506 p3564 p4137 p4381 p4625 p4661 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73260 : p2499 ∨ p2493)
    (h73340 : p3027 ∨ p2996)
    (h73524 : p4137 ∨ p3564)
    (h73288 : p2657 ∨ p2651)
    (h64014 : (¬ p2249) ∨ (¬ p2499) ∨ (¬ p2657) ∨ (¬ p3027) ∨ (¬ p3487) ∨ (¬ p3506) ∨ (¬ p4137) ∨ (¬ p4381) ∨ (¬ p4625) ∨ (¬ p4661))
    : (¬ p3506) ∨ p2761 ∨ (¬ p3487) ∨ p2493 ∨ p2996 ∨ (¬ p2249) ∨ p3564 ∨ p2651 ∨ (¬ p4661) ∨ (¬ p4625) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u13 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u14 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64014 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u14))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step82104 (p2241 p2449 p2996 p3027 p3276 p3346 p3461 p4425 p4625 p5193 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73340 : p3027 ∨ p2996)
    (h61434 : (¬ p2241) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3346) ∨ (¬ p3461) ∨ (¬ p4425) ∨ (¬ p4625) ∨ (¬ p5193))
    : p3276 ∨ (¬ p3461) ∨ (¬ p4625) ∨ p2996 ∨ (¬ p2449) ∨ (¬ p3346) ∨ (¬ p2241) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61434 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step82110 (p2284 p2992 p2996 p3027 p3662 p3952 p4333 p4558 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73440 : p3662 ∨ p2992)
    (h73340 : p3027 ∨ p2996)
    (h49631 : (¬ p3027) ∨ (¬ p3662) ∨ (¬ p3952) ∨ (¬ p4333) ∨ (¬ p4558))
    : p2284 ∨ p2992 ∨ (¬ p4333) ∨ (¬ p4558) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2284) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49631 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step82113 (p2230 p2406 p2656 p2996 p3027 p3238 p3402 p4652 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73374 : p3238 ∨ p2406)
    (h41240 : (¬ p2230) ∨ (¬ p2656) ∨ (¬ p3027) ∨ (¬ p3238) ∨ (¬ p3402) ∨ (¬ p4652))
    : (¬ p3402) ∨ p2996 ∨ p2406 ∨ (¬ p2230) ∨ (¬ p2656) ∨ (¬ p4652) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3402 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41240 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step82127 (p2241 p2383 p2387 p2449 p2996 p3027 p3266 p3322 p3461 p3950 p4191 p5021 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73246 : p2387 ∨ p2383)
    (h73340 : p3027 ∨ p2996)
    (h62166 : (¬ p2241) ∨ (¬ p2387) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3266) ∨ (¬ p3322) ∨ (¬ p3950) ∨ (¬ p4191) ∨ (¬ p5021))
    : p3461 ∨ (¬ p3266) ∨ p2383 ∨ (¬ p2241) ∨ (¬ p3322) ∨ (¬ p3950) ∨ p2996 ∨ (¬ p2449) ∨ (¬ p5021) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h62166 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step82128 (p2241 p2449 p2996 p3027 p3266 p3276 p3346 p3950 p4425 p5193 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73340 : p3027 ∨ p2996)
    (h50294 : (¬ p2241) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3266) ∨ (¬ p3346) ∨ (¬ p3950) ∨ (¬ p4425) ∨ (¬ p5193))
    : p3276 ∨ p2996 ∨ (¬ p3346) ∨ (¬ p5193) ∨ (¬ p2241) ∨ (¬ p2449) ∨ (¬ p3266) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h50294 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step82130 (p2177 p2299 p2341 p2641 p2996 p3027 p4066 p4154 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73526 : p4154 ∨ p2641)
    (h73234 : p2299 ∨ p2177)
    (h47794 : (¬ p2299) ∨ (¬ p2341) ∨ (¬ p3027) ∨ (¬ p4066) ∨ (¬ p4154))
    : p2996 ∨ (¬ p2341) ∨ (¬ p4066) ∨ p2641 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47794 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step82131 (p2341 p2881 p2996 p3027 p3246 p3570 p4066 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73340 : p3027 ∨ p2996)
    (h45792 : (¬ p2341) ∨ (¬ p3027) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p4066))
    : (¬ p3246) ∨ (¬ p2341) ∨ p2881 ∨ p2996 ∨ (¬ p4066) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45792 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step82134 (p2088 p2249 p2352 p2459 p2493 p2499 p2651 p2657 p2996 p3027 p3171 p3487 p3956 p4044 p4348 p4503 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73288 : p2657 ∨ p2651)
    (h73562 : p4348 ∨ p2459)
    (h73260 : p2499 ∨ p2493)
    (h73500 : p3956 ∨ p2352)
    (h54115 : (¬ p2088) ∨ (¬ p2249) ∨ (¬ p2499) ∨ (¬ p2657) ∨ (¬ p3027) ∨ (¬ p3171) ∨ (¬ p3487) ∨ (¬ p3956) ∨ (¬ p4044) ∨ (¬ p4348) ∨ (¬ p4503))
    : p2996 ∨ (¬ p4044) ∨ (¬ p4503) ∨ p2651 ∨ (¬ p2249) ∨ (¬ p2088) ∨ (¬ p3171) ∨ p2459 ∨ p2493 ∨ (¬ p3487) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u14 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u15 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h54115 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u14))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u15))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u13))) (fun r9 => (False.elim (r9 u2)))))))))))))))))))))))

theorem step82135 (p2132 p2138 p2241 p2264 p2996 p3027 p3146 p3609 p4340 p4359 p4736 p4905 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h73214 : p2138 ∨ p2132)
    (h73340 : p3027 ∨ p2996)
    (h59997 : (¬ p2138) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p3027) ∨ (¬ p3146) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4736) ∨ (¬ p4905))
    : p3609 ∨ p2132 ∨ (¬ p3146) ∨ (¬ p4359) ∨ (¬ p4736) ∨ (¬ p4905) ∨ (¬ p2241) ∨ (¬ p2264) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h59997 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step82136 (p2241 p2449 p2598 p2996 p3027 p3055 p3422 p3564 p3584 p4137 p4625 p4736 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73426 : p3584 ∨ p3422)
    (h73350 : p3055 ∨ p2598)
    (h73524 : p4137 ∨ p3564)
    (h61426 : (¬ p2241) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3055) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4625) ∨ (¬ p4736))
    : p2996 ∨ (¬ p2449) ∨ p3422 ∨ (¬ p2241) ∨ p2598 ∨ (¬ p4625) ∨ p3564 ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h61426 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step82137 (p2241 p2363 p2449 p2774 p2780 p2819 p2996 p3027 p3950 p4347 p4358 p4736 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73308 : p2780 ∨ p2774)
    (h73564 : p4358 ∨ p2819)
    (h73560 : p4347 ∨ p2363)
    (h53088 : (¬ p2241) ∨ (¬ p2449) ∨ (¬ p2780) ∨ (¬ p3027) ∨ (¬ p3950) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4736))
    : p2996 ∨ (¬ p2449) ∨ p2774 ∨ p2819 ∨ (¬ p2241) ∨ (¬ p4736) ∨ p2363 ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h53088 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step82139 (p2241 p2363 p2383 p2387 p2996 p3027 p3266 p3931 p4347 p4444 p4826 p5021 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73340 : p3027 ∨ p2996)
    (h73560 : p4347 ∨ p2363)
    (h73246 : p2387 ∨ p2383)
    (h41861 : (¬ p2241) ∨ (¬ p2387) ∨ (¬ p3027) ∨ (¬ p3931) ∨ (¬ p4347) ∨ (¬ p4444) ∨ (¬ p4826) ∨ (¬ p5021))
    : (¬ p3931) ∨ p3266 ∨ (¬ p5021) ∨ p2996 ∨ p2363 ∨ (¬ p4826) ∨ (¬ p2241) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3931 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h41861 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step82140 (p2241 p2573 p2579 p2996 p3027 p3461 p3564 p3931 p4137 p4191 p4826 p5193 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73524 : p4137 ∨ p3564)
    (h73274 : p2579 ∨ p2573)
    (h73340 : p3027 ∨ p2996)
    (h59446 : (¬ p2241) ∨ (¬ p2579) ∨ (¬ p3027) ∨ (¬ p3931) ∨ (¬ p4137) ∨ (¬ p4191) ∨ (¬ p4826) ∨ (¬ p5193))
    : (¬ p3931) ∨ p3461 ∨ (¬ p4826) ∨ (¬ p2241) ∨ p3564 ∨ p2573 ∨ (¬ p5193) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3931 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h59446 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step82142 (p2230 p2241 p2589 p2982 p2996 p3027 p3931 p4322 p4826 p4948 p5193 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h73340 : p3027 ∨ p2996)
    (h73846 : p4948 ∨ p2982)
    (h49987 : (¬ p2241) ∨ (¬ p2589) ∨ (¬ p3027) ∨ (¬ p3931) ∨ (¬ p4322) ∨ (¬ p4826) ∨ (¬ p4948) ∨ (¬ p5193))
    : (¬ p3931) ∨ (¬ p4322) ∨ p2230 ∨ p2996 ∨ (¬ p4826) ∨ (¬ p5193) ∨ p2982 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3931 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h49987 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step82145 (p2230 p2241 p2449 p2563 p2589 p2996 p3027 p3125 p3744 p4110 p4625 p5193 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73454 : p3744 ∨ p3125)
    (h73284 : p2589 ∨ p2230)
    (h73516 : p4110 ∨ p2563)
    (h51262 : (¬ p2241) ∨ (¬ p2449) ∨ (¬ p2589) ∨ (¬ p3027) ∨ (¬ p3744) ∨ (¬ p4110) ∨ (¬ p4625) ∨ (¬ p5193))
    : p2996 ∨ (¬ p2449) ∨ (¬ p4625) ∨ (¬ p2241) ∨ (¬ p5193) ∨ p3125 ∨ p2230 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h51262 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step82146 (p2088 p2751 p2996 p3027 p3609 p4066 p4340 p4364 p4590 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h73340 : p3027 ∨ p2996)
    (h58946 : (¬ p2088) ∨ (¬ p2751) ∨ (¬ p3027) ∨ (¬ p4066) ∨ (¬ p4340) ∨ (¬ p4364) ∨ (¬ p4590))
    : p3609 ∨ (¬ p4590) ∨ (¬ p2751) ∨ (¬ p2088) ∨ p2996 ∨ (¬ p4066) ∨ (¬ p4364) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p4590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h58946 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u1)))))))))))))))

theorem step82148 (p2230 p2241 p2427 p2589 p2996 p3027 p3125 p3744 p3872 p3931 p4235 p4396 p4830 p5193 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h73340 : p3027 ∨ p2996)
    (h73536 : p4235 ∨ p2427)
    (h73284 : p2589 ∨ p2230)
    (h41542 : (¬ p2241) ∨ (¬ p2589) ∨ (¬ p3027) ∨ (¬ p3744) ∨ (¬ p3872) ∨ (¬ p3931) ∨ (¬ p4235) ∨ (¬ p4396) ∨ (¬ p4830) ∨ (¬ p5193))
    : (¬ p3931) ∨ p3125 ∨ p2996 ∨ p2427 ∨ (¬ p4396) ∨ (¬ p4830) ∨ (¬ p5193) ∨ (¬ p2241) ∨ (¬ p3872) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3931 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h41542 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step82149 (p2761 p2996 p3027 p3266 p3516 p4066 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73340 : p3027 ∨ p2996)
    (h44949 : (¬ p2761) ∨ (¬ p3027) ∨ (¬ p3516) ∨ (¬ p4066) ∨ (¬ p4444))
    : p3266 ∨ (¬ p2761) ∨ (¬ p3516) ∨ p2996 ∨ (¬ p4066) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44949 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step82150 (p2241 p2459 p2996 p3027 p3256 p4044 p4348 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73562 : p4348 ∨ p2459)
    (h43457 : (¬ p2241) ∨ (¬ p3027) ∨ (¬ p3256) ∨ (¬ p4044) ∨ (¬ p4348))
    : p2996 ∨ (¬ p2241) ∨ p2459 ∨ (¬ p4044) ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43457 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step82151 (p2187 p2274 p2396 p3097 p3550 p4107 p4666 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73352 : p3097 ∨ p2274)
    (h61979 : (¬ p2187) ∨ (¬ p3097) ∨ (¬ p3550) ∨ (¬ p4107) ∨ (¬ p4666))
    : p2396 ∨ p2274 ∨ (¬ p4666) ∨ (¬ p2187) ∨ (¬ p3550) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2396) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h61979 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step82153 (p2241 p2253 p2256 : Prop)
    (h73231 : (¬ p2241) ∨ (¬ p2256))
    (h2643 : p2253 ∨ p2256)
    : p2253 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2253) := (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2256) := (Or.elim h73231 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h2643 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step82160 (p2264 p2449 p3553 p3657 p3947 : Prop)
    (h73493 : (¬ p2449) ∨ (¬ p3947))
    (h73410 : p3553 ∨ p2264)
    (h6886 : (¬ p3553) ∨ (¬ p3657) ∨ p3947)
    : (¬ p2449) ∨ (¬ p3657) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3947) := (Or.elim h73493 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h6886 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u3 r1)))))))

theorem step82162 (p2449 p3516 p3821 p3947 p4155 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73493 : (¬ p2449) ∨ (¬ p3947))
    (h23017 : (¬ p3821) ∨ p3947 ∨ (¬ p4155))
    : p3516 ∨ (¬ p2449) ∨ (¬ p4155) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p3947) := (Or.elim h73493 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h23017 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step82164 (p2417 p2449 p3740 p3947 p4278 : Prop)
    (h73493 : (¬ p2449) ∨ (¬ p3947))
    (h73546 : p4278 ∨ p2417)
    (h35980 : (¬ p3740) ∨ p3947 ∨ (¬ p4278))
    : (¬ p2449) ∨ p2417 ∨ (¬ p3740) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3947) := (Or.elim h73493 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h35980 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step82173 (p2641 p2741 p2797 p2839 p4154 p5052 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h62019 : (¬ p2741) ∨ (¬ p2797) ∨ (¬ p2839) ∨ (¬ p4154) ∨ (¬ p5052))
    : p2641 ∨ (¬ p2797) ∨ (¬ p2839) ∨ (¬ p5052) ∨ (¬ p2741) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5052 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h62019 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step82176 (p2727 p4281 p4812 : Prop)
    (h73772 : p4812 ∨ (¬ p2727))
    (h7862 : p4281 ∨ (¬ p4812))
    : p4281 ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4281) := (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4812 := (Or.elim h73772 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h7862 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step82178 (p2727 p4812 p4814 : Prop)
    (h73772 : p4812 ∨ (¬ p2727))
    (h7865 : (¬ p4812) ∨ p4814)
    : (¬ p2727) ∨ p4814 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4814) := (fun h => hn (Or.inr h));
    let u2 : p4812 := (Or.elim h73772 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h7865 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step82179 (p2630 p2651 p2657 p2727 p2751 p2810 p3379 p4812 : Prop)
    (h73772 : p4812 ∨ (¬ p2727))
    (h73288 : p2657 ∨ p2651)
    (h73316 : p2810 ∨ p2630)
    (h66648 : (¬ p4812) ∨ (¬ p2810) ∨ (¬ p2751) ∨ (¬ p2657) ∨ (¬ p3379))
    : (¬ p2727) ∨ (¬ p2751) ∨ p2651 ∨ (¬ p3379) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4812 := (Or.elim h73772 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h66648 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step82180 (p2651 p2657 p2727 p2992 p3166 p3662 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73288 : p2657 ∨ p2651)
    (h47752 : (¬ p2657) ∨ (¬ p2727) ∨ (¬ p3166) ∨ (¬ p3662))
    : p2992 ∨ (¬ p3166) ∨ (¬ p2727) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47752 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step82184 (p2651 p2657 p2727 p2797 p3323 p3361 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h45036 : (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3361))
    : (¬ p3323) ∨ (¬ p2797) ∨ p2651 ∨ (¬ p2727) ∨ (¬ p3361) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45036 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step82186 (p2449 p2651 p2657 p2727 p2807 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h44935 : (¬ p2449) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2807))
    : (¬ p2449) ∨ (¬ p2727) ∨ p2651 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44935 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step82190 (p2651 p2657 p2727 p2807 p2911 p3579 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h44943 : (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2807) ∨ (¬ p2911) ∨ (¬ p3579))
    : (¬ p2727) ∨ (¬ p3579) ∨ p2651 ∨ (¬ p2911) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44943 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step82191 (p2641 p2651 p2657 p2727 p2946 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73288 : p2657 ∨ p2651)
    (h59105 : (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2946) ∨ (¬ p4154))
    : p2641 ∨ (¬ p2946) ∨ (¬ p2727) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h59105 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step82192 (p2528 p2534 p2651 p2657 p2727 p3189 p4360 p4437 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73268 : p2534 ∨ p2528)
    (h73288 : p2657 ∨ p2651)
    (h47795 : (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p4360) ∨ (¬ p4437))
    : p3189 ∨ (¬ p2727) ∨ p2528 ∨ (¬ p4437) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47795 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step82195 (p2341 p2651 p2657 p2727 p2911 p3644 p4104 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73288 : p2657 ∨ p2651)
    (h50109 : (¬ p2341) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p3644) ∨ (¬ p4104))
    : (¬ p2341) ∨ p2911 ∨ p2651 ∨ (¬ p2727) ∨ (¬ p4104) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2911) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50109 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step82196 (p2284 p2651 p2657 p2727 p2946 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h43270 : (¬ p2284) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2946))
    : (¬ p2946) ∨ (¬ p2727) ∨ (¬ p2284) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43270 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step82198 (p2651 p2657 p2727 p3166 p3256 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h48744 : (¬ p2657) ∨ (¬ p2727) ∨ (¬ p3166) ∨ (¬ p3256))
    : (¬ p3166) ∨ (¬ p3256) ∨ p2651 ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48744 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step82202 (p2427 p2651 p2657 p2727 p2891 p3368 p3486 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73398 : p3486 ∨ p2891)
    (h62215 : (¬ p2427) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p3368) ∨ (¬ p3486))
    : (¬ p2727) ∨ (¬ p3368) ∨ p2651 ∨ (¬ p2427) ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62215 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step82203 (p2210 p2245 p2651 p2657 p2727 p4959 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h52510 : (¬ p2210) ∨ (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p4959))
    : (¬ p2727) ∨ (¬ p2245) ∨ (¬ p4959) ∨ (¬ p2210) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h52510 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step82205 (p2241 p2608 p2630 p2727 p2810 p3954 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73316 : p2810 ∨ p2630)
    (h54548 : (¬ p2241) ∨ (¬ p2727) ∨ (¬ p2810) ∨ (¬ p3954))
    : (¬ p2727) ∨ p2608 ∨ p2630 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h54548 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step82208 (p2331 p2630 p2641 p2727 p2810 p4154 p4790 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73316 : p2810 ∨ p2630)
    (h53490 : (¬ p2331) ∨ (¬ p2727) ∨ (¬ p2810) ∨ (¬ p4154) ∨ (¬ p4790))
    : p2641 ∨ (¬ p2331) ∨ (¬ p4790) ∨ (¬ p2727) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h53490 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step82211 (p2331 p2553 p2651 p2657 p2727 p3984 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h47852 : (¬ p2331) ∨ (¬ p2553) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p3984))
    : (¬ p2331) ∨ (¬ p2553) ∨ p2651 ∨ (¬ p2727) ∨ (¬ p3984) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47852 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step82212 (p2573 p2579 p2727 p2751 p3016 p3363 p3364 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h55742 : (¬ p2579) ∨ (¬ p2727) ∨ (¬ p2751) ∨ (¬ p3016) ∨ (¬ p3363) ∨ (¬ p3364))
    : (¬ p2751) ∨ p2573 ∨ (¬ p2727) ∨ (¬ p3363) ∨ (¬ p3364) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2751 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h55742 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step82214 (p2295 p2331 p2651 p2657 p2727 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h56059 : (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2657) ∨ (¬ p2727))
    : (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2727) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56059 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step82216 (p2641 p2651 p2657 p2727 p2797 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73288 : p2657 ∨ p2651)
    (h71535 : (¬ p4154) ∨ (¬ p2797) ∨ (¬ p2657) ∨ (¬ p2727))
    : p2641 ∨ (¬ p2797) ∨ p2651 ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h71535 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step82223 (p2156 p2177 p2245 p2274 p2651 p2657 p2727 p3189 p4041 p4360 p4521 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73288 : p2657 ∨ p2651)
    (h51520 : (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2245) ∨ (¬ p2274) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p4041) ∨ (¬ p4360) ∨ (¬ p4521))
    : (¬ p2245) ∨ (¬ p4521) ∨ (¬ p2156) ∨ (¬ p2727) ∨ (¬ p2177) ∨ p3189 ∨ (¬ p4041) ∨ p2651 ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h51520 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step82227 (p2156 p2187 p2241 p2363 p2727 p3343 p3646 p3989 p4332 p4347 p4524 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73436 : p3646 ∨ p2156)
    (h73502 : p3989 ∨ p2187)
    (h72962 : p4524)
    (h52225 : (¬ p2241) ∨ (¬ p2727) ∨ (¬ p3343) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4332) ∨ (¬ p4347) ∨ (¬ p4524))
    : (¬ p3343) ∨ p2363 ∨ p2156 ∨ (¬ p2241) ∨ (¬ p4332) ∨ p2187 ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p4524 := h72962;
    (Or.elim h52225 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u10)))))))))))))))))

theorem step82231 (p2245 p2295 p2641 p2651 p2657 p2727 p3568 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73288 : p2657 ∨ p2651)
    (h73416 : p3568 ∨ p2295)
    (h55668 : (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p3568) ∨ (¬ p4154))
    : p2641 ∨ (¬ p2245) ∨ p2651 ∨ p2295 ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55668 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step82236 (p2136 p2156 p2177 p2241 p2274 p2299 p2727 p3083 p3097 p3646 p4420 p4736 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73352 : p3097 ∨ p2274)
    (h73234 : p2299 ∨ p2177)
    (h60549 : (¬ p2136) ∨ (¬ p2241) ∨ (¬ p2299) ∨ (¬ p2727) ∨ (¬ p3083) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4420) ∨ (¬ p4736))
    : (¬ p3083) ∨ p2156 ∨ (¬ p4736) ∨ p2274 ∨ (¬ p4420) ∨ (¬ p2136) ∨ p2177 ∨ (¬ p2727) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3083 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h60549 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step82237 (p2427 p2563 p2656 p2727 p3051 p4235 p4399 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h62732 : (¬ p2563) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p3051) ∨ (¬ p4235) ∨ (¬ p4399))
    : (¬ p3051) ∨ p2427 ∨ (¬ p2563) ∨ (¬ p4399) ∨ (¬ p2656) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h62732 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step82239 (p2187 p2241 p2383 p2387 p2727 p3125 p3343 p3744 p4198 p4524 p5322 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h73454 : p3744 ∨ p3125)
    (h72962 : p4524)
    (h57369 : (¬ p2187) ∨ (¬ p2241) ∨ (¬ p2387) ∨ (¬ p2727) ∨ (¬ p3343) ∨ (¬ p3744) ∨ (¬ p4198) ∨ (¬ p4524) ∨ (¬ p5322))
    : (¬ p3343) ∨ (¬ p2187) ∨ (¬ p5322) ∨ (¬ p2241) ∨ p2383 ∨ (¬ p4198) ∨ p3125 ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u10 : p4524 := h72962;
    (Or.elim h57369 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step82240 (p2241 p2619 p2727 p2870 p3051 p3083 p3556 p3694 p4158 p4524 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h72962 : p4524)
    (h73450 : p3694 ∨ p2619)
    (h63378 : (¬ p2241) ∨ (¬ p2727) ∨ (¬ p2870) ∨ (¬ p3083) ∨ (¬ p3556) ∨ (¬ p3694) ∨ (¬ p4158) ∨ (¬ p4524))
    : (¬ p2241) ∨ (¬ p3083) ∨ (¬ p2870) ∨ (¬ p2727) ∨ p3051 ∨ p2619 ∨ (¬ p4158) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4158 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u8 : p4524 := h72962;
    let u9 : p3694 := (Or.elim h73450 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h63378 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u8)))))))))))))))))

theorem step82241 (p2459 p2470 p2528 p2656 p2727 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h64015 : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p4348))
    : (¬ p2470) ∨ (¬ p2656) ∨ p2459 ∨ (¬ p2528) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h64015 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step82243 (p2641 p2656 p2727 p2911 p3389 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h44942 : (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p4154))
    : p2641 ∨ (¬ p3389) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h44942 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step82244 (p2396 p2417 p2727 p2996 p3575 p4155 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h45065 : (¬ p2396) ∨ (¬ p2727) ∨ (¬ p2996) ∨ (¬ p3575) ∨ (¬ p4155) ∨ (¬ p4278))
    : p2417 ∨ (¬ p2996) ∨ (¬ p2727) ∨ (¬ p2396) ∨ (¬ p4155) ∨ (¬ p3575) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45065 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step82245 (p2156 p2727 p2901 p3051 p3413 p3556 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h44947 : (¬ p2156) ∨ (¬ p2727) ∨ (¬ p2901) ∨ (¬ p3413) ∨ (¬ p3556))
    : (¬ p2901) ∨ p3051 ∨ (¬ p2156) ∨ (¬ p2727) ∨ (¬ p3413) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h44947 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step82247 (p2295 p2553 p2641 p2727 p3568 p4154 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73526 : p4154 ∨ p2641)
    (h44623 : (¬ p2553) ∨ (¬ p2727) ∨ (¬ p3568) ∨ (¬ p4154))
    : p2295 ∨ p2641 ∨ (¬ p2553) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2295) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h44623 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step82253 (p2651 p2657 p2727 p3286 p3506 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h44934 : (¬ p2657) ∨ (¬ p2727) ∨ (¬ p3286) ∨ (¬ p3506))
    : (¬ p3286) ∨ (¬ p3506) ∨ p2651 ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3286 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44934 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step82259 (p2284 p2563 p2727 p2992 p3662 p3952 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73496 : p3952 ∨ p2284)
    (h47222 : (¬ p2563) ∨ (¬ p2727) ∨ (¬ p3662) ∨ (¬ p3952))
    : p2992 ∨ p2284 ∨ (¬ p2727) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47222 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step82260 (p2245 p2284 p2651 p2657 p2727 p2992 p3662 p3952 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73496 : p3952 ∨ p2284)
    (h73288 : p2657 ∨ p2651)
    (h44003 : (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p3662) ∨ (¬ p3952))
    : p2992 ∨ (¬ p2727) ∨ p2284 ∨ p2651 ∨ (¬ p2245) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44003 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step82264 (p2373 p2727 p2992 p3156 p3497 p3662 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73400 : p3497 ∨ p3156)
    (h52868 : (¬ p2373) ∨ (¬ p2727) ∨ (¬ p3497) ∨ (¬ p3662))
    : p2992 ∨ p3156 ∨ (¬ p2727) ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h52868 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step82265 (p2619 p2727 p2992 p3156 p3497 p3662 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73400 : p3497 ∨ p3156)
    (h47218 : (¬ p2619) ∨ (¬ p2727) ∨ (¬ p3497) ∨ (¬ p3662))
    : p2992 ∨ (¬ p2619) ∨ (¬ p2727) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47218 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step82267 (p2220 p2727 p2992 p3156 p3497 p3662 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73400 : p3497 ∨ p3156)
    (h52866 : (¬ p2220) ∨ (¬ p2727) ∨ (¬ p3497) ∨ (¬ p3662))
    : p2992 ∨ (¬ p2220) ∨ p3156 ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52866 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step82272 (p2088 p2727 p3073 p4066 p4261 p4262 p4590 p4650 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h63911 : (¬ p2088) ∨ (¬ p2727) ∨ (¬ p4066) ∨ (¬ p4261) ∨ (¬ p4262) ∨ (¬ p4590) ∨ (¬ p4650))
    : p3073 ∨ (¬ p4066) ∨ (¬ p2727) ∨ (¬ p4650) ∨ (¬ p2088) ∨ (¬ p4590) ∨ (¬ p4262) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4262 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h63911 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step82275 (p2274 p2553 p2578 p2588 p2641 p2667 p2727 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73282 : p2588 ∨ p2553)
    (h63862 : (¬ p2274) ∨ (¬ p2578) ∨ (¬ p2588) ∨ (¬ p2667) ∨ (¬ p2727) ∨ (¬ p4154))
    : p2641 ∨ (¬ p2274) ∨ (¬ p2578) ∨ (¬ p2667) ∨ p2553 ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63862 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step82276 (p2307 p2553 p2584 p2588 p2656 p2727 p3564 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h57809 : (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p3564))
    : (¬ p3564) ∨ (¬ p2307) ∨ p2553 ∨ (¬ p2727) ∨ (¬ p2584) ∨ (¬ p2656) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h57809 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step82281 (p2274 p2553 p2573 p2656 p2727 p3097 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h64414 : (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p3097))
    : (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2727) ∨ (¬ p2656) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h64414 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step82282 (p2249 p2264 p2553 p2573 p2656 p2727 p2807 p2881 p3414 p3553 p4559 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h73392 : p3414 ∨ p2807)
    (h64589 : (¬ p2249) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2881) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4559))
    : (¬ p2553) ∨ (¬ p2656) ∨ p2264 ∨ p2807 ∨ (¬ p2727) ∨ (¬ p4559) ∨ (¬ p2573) ∨ (¬ p2881) ∨ (¬ p2249) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h64589 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step82285 (p2341 p2417 p2656 p2727 p2911 p3644 p5201 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h59113 : (¬ p2341) ∨ (¬ p2417) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p3644) ∨ (¬ p5201))
    : (¬ p2341) ∨ (¬ p2417) ∨ p2911 ∨ (¬ p5201) ∨ (¬ p2656) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h59113 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step82288 (p2470 p2665 p2727 p3189 p4360 p4437 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h63169 : (¬ p2470) ∨ (¬ p2665) ∨ (¬ p2727) ∨ (¬ p4360) ∨ (¬ p4437))
    : p3189 ∨ (¬ p2470) ∨ (¬ p2727) ∨ (¬ p2665) ∨ (¬ p4437) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h63169 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step82290 (p2656 p2727 p2881 p2911 p3389 p3570 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h46401 : (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3570))
    : (¬ p2911) ∨ (¬ p2656) ∨ (¬ p3389) ∨ p2881 ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46401 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step82291 (p2656 p2727 p2992 p3389 p3662 p3879 p4646 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h41494 : (¬ p2656) ∨ (¬ p2727) ∨ (¬ p3389) ∨ (¬ p3662) ∨ (¬ p3879) ∨ (¬ p4646))
    : p2992 ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p4646) ∨ (¬ p3389) ∨ (¬ p3879) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41494 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step82293 (p2220 p2249 p2331 p2363 p2656 p2727 p2963 p3922 p3923 p3969 p4347 p4399 p5122 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73338 : p2963 ∨ p2331)
    (h53685 : (¬ p2220) ∨ (¬ p2249) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2963) ∨ (¬ p3922) ∨ (¬ p3923) ∨ (¬ p3969) ∨ (¬ p4347) ∨ (¬ p4399) ∨ (¬ p5122))
    : (¬ p3969) ∨ p2363 ∨ (¬ p2656) ∨ (¬ p2249) ∨ (¬ p3923) ∨ (¬ p4399) ∨ (¬ p2220) ∨ p2331 ∨ (¬ p2727) ∨ (¬ p3922) ∨ (¬ p5122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h53685 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u5))) (fun r9 => (False.elim (r9 u10)))))))))))))))))))))))

theorem step82294 (p2156 p2656 p2727 p2751 p2860 p3758 p4392 p4399 : Prop)
    (h73456 : p3758 ∨ p2860)
    (h42252 : (¬ p2156) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2751) ∨ (¬ p3758) ∨ (¬ p4392) ∨ (¬ p4399))
    : (¬ p4399) ∨ (¬ p2751) ∨ p2860 ∨ (¬ p2156) ∨ (¬ p2656) ∨ (¬ p4392) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42252 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u0)))))))))))))))

theorem step82295 (p2656 p2727 p2870 p3105 p3212 p4385 p4399 : Prop)
    (h73576 : p4385 ∨ p3105)
    (h61236 : (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2870) ∨ (¬ p3212) ∨ (¬ p4385) ∨ (¬ p4399))
    : (¬ p4399) ∨ p3105 ∨ (¬ p2656) ∨ (¬ p2870) ∨ (¬ p2727) ∨ (¬ p3212) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3105) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4385 := (Or.elim h73576 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h61236 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step82296 (p2230 p2665 p2727 p2992 p3662 p3879 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h41033 : (¬ p2230) ∨ (¬ p2665) ∨ (¬ p2727) ∨ (¬ p3662) ∨ (¬ p3879))
    : p2992 ∨ (¬ p2230) ∨ (¬ p2665) ∨ (¬ p2727) ∨ (¬ p3879) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41033 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step82297 (p2230 p2641 p2656 p2727 p4154 p4389 p4715 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h51526 : (¬ p2230) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p4154) ∨ (¬ p4389) ∨ (¬ p4715))
    : p2641 ∨ (¬ p2230) ∨ (¬ p2727) ∨ (¬ p2656) ∨ (¬ p4715) ∨ (¬ p4389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h51526 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step82298 (p2230 p2656 p2727 p2751 p2850 p3364 p3684 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h41750 : (¬ p2230) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2751) ∨ (¬ p3364) ∨ (¬ p3684))
    : (¬ p3364) ∨ (¬ p2751) ∨ (¬ p2727) ∨ (¬ p2230) ∨ (¬ p2656) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3364 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41750 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step82299 (p2230 p2249 p2373 p2459 p2656 p2727 p2807 p3037 p3073 p3414 p3544 p4261 p4902 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h73392 : p3414 ∨ p2807)
    (h64788 : (¬ p2230) ∨ (¬ p2249) ∨ (¬ p2373) ∨ (¬ p2459) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p3037) ∨ (¬ p3414) ∨ (¬ p3544) ∨ (¬ p4261) ∨ (¬ p4902))
    : (¬ p3037) ∨ (¬ p2373) ∨ (¬ p2459) ∨ p3073 ∨ (¬ p2727) ∨ p2807 ∨ (¬ p2656) ∨ (¬ p4902) ∨ (¬ p2249) ∨ (¬ p2230) ∨ (¬ p3544) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3037 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3544 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h64788 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u11))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step82301 (p2427 p2656 p2727 p2982 p3212 p4399 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h44953 : (¬ p2427) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p3212) ∨ (¬ p4399) ∨ (¬ p4948))
    : (¬ p4399) ∨ (¬ p2656) ∨ p2982 ∨ (¬ p3212) ∨ (¬ p2427) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44953 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step82303 (p2122 p2177 p2245 p2651 p2657 p2727 p2774 p3189 p4360 p4437 p4438 p4733 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73288 : p2657 ∨ p2651)
    (h58836 : (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2774) ∨ (¬ p4360) ∨ (¬ p4437) ∨ (¬ p4438) ∨ (¬ p4733))
    : (¬ p2245) ∨ (¬ p2122) ∨ (¬ p4438) ∨ (¬ p4437) ∨ p3189 ∨ (¬ p2774) ∨ (¬ p2177) ∨ p2651 ∨ (¬ p2727) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h58836 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step82307 (p2241 p2440 p2542 p2727 p2982 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h43736 : (¬ p2241) ∨ (¬ p2542) ∨ (¬ p2727) ∨ (¬ p2982))
    : (¬ p2727) ∨ (¬ p2982) ∨ (¬ p2241) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43736 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step82309 (p2230 p2249 p2440 p2542 p2589 p2727 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73284 : p2589 ∨ p2230)
    (h68067 : (¬ p2589) ∨ (¬ p2727) ∨ (¬ p2249) ∨ (¬ p2542))
    : (¬ p2727) ∨ (¬ p2249) ∨ p2440 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h68067 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step82311 (p2440 p2542 p2727 p3189 p4360 p4437 p4608 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73270 : p2542 ∨ p2440)
    (h48130 : (¬ p2542) ∨ (¬ p2727) ∨ (¬ p4360) ∨ (¬ p4437) ∨ (¬ p4608))
    : p3189 ∨ (¬ p2727) ∨ (¬ p4437) ∨ p2440 ∨ (¬ p4608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48130 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step82312 (p2440 p2542 p2727 p3848 p4949 p5171 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h63856 : (¬ p2542) ∨ (¬ p2727) ∨ (¬ p3848) ∨ (¬ p4949) ∨ (¬ p5171))
    : (¬ p3848) ∨ (¬ p2727) ∨ (¬ p4949) ∨ p2440 ∨ (¬ p5171) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3848 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4949 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63856 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step82313 (p2331 p2440 p2542 p2641 p2727 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73270 : p2542 ∨ p2440)
    (h45399 : (¬ p2331) ∨ (¬ p2542) ∨ (¬ p2727) ∨ (¬ p4154))
    : (¬ p2331) ∨ p2641 ∨ (¬ p2727) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45399 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step82314 (p2440 p2542 p2727 p3166 p3189 p4360 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73270 : p2542 ∨ p2440)
    (h58300 : (¬ p2542) ∨ (¬ p2727) ∨ (¬ p3166) ∨ (¬ p4360))
    : p3189 ∨ (¬ p3166) ∨ p2440 ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h58300 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step82315 (p2440 p2542 p2727 p2807 p2996 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h50360 : (¬ p2542) ∨ (¬ p2727) ∨ (¬ p2807) ∨ (¬ p2996))
    : (¬ p2996) ∨ (¬ p2727) ∨ p2440 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50360 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step82316 (p2727 p2996 p3027 p3580 : Prop)
    (h73339 : (¬ p2996) ∨ (¬ p3027))
    (h22993 : (¬ p2727) ∨ p3027 ∨ (¬ p3580))
    : (¬ p2996) ∨ (¬ p3580) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3027) := (Or.elim h73339 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    (Or.elim h22993 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step82319 (p2241 p2437 p2727 p3201 p3876 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h55119 : (¬ p2241) ∨ (¬ p2437) ∨ (¬ p2727) ∨ (¬ p3876))
    : p3201 ∨ (¬ p2437) ∨ (¬ p2241) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h55119 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step82320 (p2156 p2563 p2727 p2957 p2992 p3646 p3662 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73436 : p3646 ∨ p2156)
    (h60343 : (¬ p2563) ∨ (¬ p2727) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3662))
    : p2992 ∨ (¬ p2957) ∨ (¬ p2563) ∨ (¬ p2727) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h60343 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step82322 (p2241 p2427 p2440 p2542 p2727 p4204 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h50205 : (¬ p2241) ∨ (¬ p2427) ∨ (¬ p2542) ∨ (¬ p2727) ∨ (¬ p4204))
    : (¬ p4204) ∨ (¬ p2727) ∨ (¬ p2241) ∨ (¬ p2427) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4204 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50205 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step82323 (p2727 p3506 p3707 p3846 p4321 p5008 p5111 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h50598 : (¬ p2727) ∨ (¬ p3506) ∨ (¬ p3846) ∨ (¬ p4321) ∨ (¬ p5008) ∨ (¬ p5111))
    : p3707 ∨ (¬ p3846) ∨ (¬ p2727) ∨ (¬ p5008) ∨ (¬ p5111) ∨ (¬ p3506) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : p3846 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5008 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h50598 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step82324 (p2220 p2245 p2459 p2651 p2657 p2727 p3146 p3189 p4041 p4348 p4360 p4521 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73562 : p4348 ∨ p2459)
    (h73288 : p2657 ∨ p2651)
    (h55762 : (¬ p2220) ∨ (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p3146) ∨ (¬ p4041) ∨ (¬ p4348) ∨ (¬ p4360) ∨ (¬ p4521))
    : p3189 ∨ (¬ p4041) ∨ p2459 ∨ p2651 ∨ (¬ p3146) ∨ (¬ p2220) ∨ (¬ p2245) ∨ (¬ p2727) ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55762 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step82326 (p2427 p2727 p2957 p2992 p3051 p3556 p3662 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73414 : p3556 ∨ p3051)
    (h45383 : (¬ p2427) ∨ (¬ p2727) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3662))
    : p2992 ∨ (¬ p2957) ∨ (¬ p2427) ∨ (¬ p2727) ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45383 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step82329 (p2427 p3569 p5855 : Prop)
    (h74151 : (¬ p2427) ∨ (¬ p5855))
    (h12123 : p3569 ∨ p5855)
    : p3569 ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3569) := (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5855) := (Or.elim h74151 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12123 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step82330 (p2246 p2528 p2608 p2651 p2744 p3083 p3399 p3631 p3817 p4366 p4669 : Prop)
    (h73468 : p3817 ∨ p3631)
    (h73570 : p4366 ∨ p3399)
    (h52869 : (¬ p2246) ∨ (¬ p2528) ∨ (¬ p2608) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4669))
    : (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2528) ∨ p3631 ∨ (¬ p2744) ∨ (¬ p3083) ∨ p3399 ∨ (¬ p2651) ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h52869 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step82333 (p2187 p2246 p2284 p2608 p2744 p2946 p3093 p3309 p3549 p3591 p4405 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73406 : p3549 ∨ p3309)
    (h56524 : (¬ p2187) ∨ (¬ p2246) ∨ (¬ p2284) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4405))
    : p3093 ∨ (¬ p2246) ∨ (¬ p2187) ∨ (¬ p2608) ∨ (¬ p4405) ∨ p3309 ∨ (¬ p2744) ∨ (¬ p2284) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h56524 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step82338 (p2246 p2957 p2958 p2992 p3662 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h12777 : (¬ p2246) ∨ (¬ p2957) ∨ (¬ p2958) ∨ (¬ p3662))
    : (¬ p2246) ∨ p2992 ∨ (¬ p2957) ∨ (¬ p2958) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h12777 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step82339 (p2156 p2246 p2608 p2744 p2958 p3399 p3461 p3506 p3631 p3745 p3817 p4191 p4366 p4421 p4621 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73468 : p3817 ∨ p3631)
    (h73570 : p4366 ∨ p3399)
    (h55911 : (¬ p2156) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2958) ∨ (¬ p3506) ∨ (¬ p3745) ∨ (¬ p3817) ∨ (¬ p4191) ∨ (¬ p4366) ∨ (¬ p4421) ∨ (¬ p4621))
    : (¬ p3506) ∨ p3461 ∨ p3631 ∨ p3399 ∨ (¬ p2156) ∨ (¬ p4621) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2958) ∨ (¬ p2608) ∨ (¬ p4421) ∨ (¬ p3745) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4421 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u13 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u14 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55911 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u13))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u14))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u10))) (fun r10 => (False.elim (r10 u5)))))))))))))))))))))))))

theorem step82340 (p2246 p2427 p2563 p2727 p2958 p3051 p4111 p4235 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73536 : p4235 ∨ p2427)
    (h53314 : (¬ p2246) ∨ (¬ p2563) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p4111) ∨ (¬ p4235))
    : (¬ p2246) ∨ p2727 ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p2563) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h53314 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step82342 (p2246 p2727 p2807 p2881 p2911 p3570 p3579 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73418 : p3570 ∨ p2881)
    (h53893 : (¬ p2246) ∨ (¬ p2807) ∨ (¬ p2911) ∨ (¬ p3570) ∨ (¬ p3579) ∨ (¬ p4111))
    : p2727 ∨ (¬ p2911) ∨ (¬ p3579) ∨ (¬ p2246) ∨ (¬ p2807) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h53893 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step82343 (p2246 p2807 p2996 p3414 : Prop)
    (h73391 : (¬ p2807) ∨ (¬ p3414))
    (h21894 : (¬ p2246) ∨ (¬ p2996) ∨ p3414)
    : (¬ p2996) ∨ (¬ p2246) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3414) := (Or.elim h73391 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h21894 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u3 r1)))))))

theorem step82346 (p2246 p2807 p2870 p2992 p3662 p4244 p4333 p4906 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73540 : p4244 ∨ p2870)
    (h41632 : (¬ p2246) ∨ (¬ p2807) ∨ (¬ p3662) ∨ (¬ p4244) ∨ (¬ p4333) ∨ (¬ p4906))
    : p2992 ∨ (¬ p2246) ∨ (¬ p4906) ∨ p2870 ∨ (¬ p2807) ∨ (¬ p4333) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41632 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step82349 (p2156 p2246 p2284 p2608 p2744 p2958 p3156 p3399 p3527 p3548 p3952 p4366 p4902 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73570 : p4366 ∨ p3399)
    (h73404 : p3548 ∨ p3527)
    (h52825 : (¬ p2156) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2958) ∨ (¬ p3156) ∨ (¬ p3548) ∨ (¬ p3952) ∨ (¬ p4366) ∨ (¬ p4902))
    : (¬ p3156) ∨ p2284 ∨ (¬ p2156) ∨ (¬ p4902) ∨ (¬ p2958) ∨ p3399 ∨ p3527 ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h52825 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step82351 (p2246 p2751 p2870 p2901 p2946 p4244 p4392 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h41648 : (¬ p2246) ∨ (¬ p2751) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p4244) ∨ (¬ p4392))
    : (¬ p2901) ∨ (¬ p2246) ∨ p2870 ∨ (¬ p2946) ∨ (¬ p2751) ∨ (¬ p4392) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41648 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step82355 (p2246 p2284 p2946 p3189 p3256 p4118 p4360 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73520 : p4118 ∨ p3256)
    (h55520 : (¬ p2246) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p4118) ∨ (¬ p4360))
    : p3189 ∨ (¬ p2246) ∨ (¬ p2946) ∨ (¬ p2284) ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55520 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step82357 (p2246 p2264 p2727 p2807 p2881 p3570 p4111 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73518 : p4111 ∨ p2727)
    (h46374 : (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p3570) ∨ (¬ p4111))
    : (¬ p2264) ∨ p2881 ∨ (¬ p2807) ∨ p2727 ∨ (¬ p2246) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46374 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step82359 (p2246 p2459 p3189 p3286 p4041 p4348 p4350 p4360 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73566 : p4360 ∨ p3189)
    (h41748 : (¬ p2246) ∨ (¬ p3286) ∨ (¬ p4041) ∨ (¬ p4348) ∨ (¬ p4350) ∨ (¬ p4360))
    : (¬ p2246) ∨ (¬ p3286) ∨ p2459 ∨ p3189 ∨ (¬ p4041) ∨ (¬ p4350) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4350 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41748 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step82363 (p2246 p2807 p2992 p3662 p4386 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h26772 : (¬ p2246) ∨ (¬ p2807) ∨ (¬ p3662) ∨ (¬ p4386))
    : p2992 ∨ (¬ p2246) ∨ (¬ p4386) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h26772 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step82365 (p2246 p2651 p2727 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h15060 : (¬ p2246) ∨ (¬ p2651) ∨ (¬ p4111))
    : p2727 ∨ (¬ p2246) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h15060 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step82369 (p2246 p2383 p2668 p2727 p3324 p3987 p4111 p4975 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73386 : p3324 ∨ p2668)
    (h50649 : (¬ p2246) ∨ (¬ p2383) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p4111) ∨ (¬ p4975))
    : (¬ p2383) ∨ (¬ p2246) ∨ (¬ p3987) ∨ p2727 ∨ (¬ p4975) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h50649 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step82375 (p2246 p2608 p2744 p2958 p3073 p3212 p3449 p3461 p3506 p3860 p4040 p4191 p4261 p4330 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73544 : p4261 ∨ p3073)
    (h73482 : p3860 ∨ p3449)
    (h58393 : (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2958) ∨ (¬ p3212) ∨ (¬ p3506) ∨ (¬ p3860) ∨ (¬ p4040) ∨ (¬ p4191) ∨ (¬ p4261) ∨ (¬ p4330))
    : (¬ p3506) ∨ p3461 ∨ (¬ p3212) ∨ p3073 ∨ (¬ p2744) ∨ p3449 ∨ (¬ p4040) ∨ (¬ p2608) ∨ (¬ p4330) ∨ (¬ p2246) ∨ (¬ p2958) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4040 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h58393 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (False.elim (r9 u8)))))))))))))))))))))))

theorem step82378 (p2246 p2440 p2727 p2807 p3579 p4111 p4646 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h52418 : (¬ p2246) ∨ (¬ p2440) ∨ (¬ p2807) ∨ (¬ p3579) ∨ (¬ p4111) ∨ (¬ p4646))
    : (¬ p2246) ∨ p2727 ∨ (¬ p4646) ∨ (¬ p3579) ∨ (¬ p2807) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h52418 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step82379 (p2246 p2417 p2437 p2608 p2651 p2744 p2881 p3399 p3570 p4366 p4668 p4909 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73418 : p3570 ∨ p2881)
    (h61679 : (¬ p2246) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2608) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3570) ∨ (¬ p4366) ∨ (¬ p4668) ∨ (¬ p4909))
    : (¬ p2246) ∨ p3399 ∨ p2881 ∨ (¬ p2608) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p4668) ∨ (¬ p4909) ∨ (¬ p2417) ∨ (¬ p2744) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4909 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h61679 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step82380 (p2246 p2437 p2608 p2651 p2744 p2911 p3399 p3631 p3817 p4366 p4666 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73468 : p3817 ∨ p3631)
    (h52714 : (¬ p2246) ∨ (¬ p2437) ∨ (¬ p2608) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2911) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4666))
    : p3399 ∨ (¬ p2911) ∨ (¬ p2608) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p4666) ∨ p3631 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h52714 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step82381 (p2177 p2246 p2264 p2299 p2331 p2992 p3662 p4156 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73234 : p2299 ∨ p2177)
    (h46026 : (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2299) ∨ (¬ p2331) ∨ (¬ p3662) ∨ (¬ p4156))
    : p2992 ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p4156) ∨ (¬ p2264) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h46026 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step82385 (p2246 p2331 p2363 p2608 p2744 p3256 p3399 p3527 p3548 p4133 p4341 p4347 p4366 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73404 : p3548 ∨ p3527)
    (h73570 : p4366 ∨ p3399)
    (h52777 : (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3256) ∨ (¬ p3548) ∨ (¬ p4133) ∨ (¬ p4341) ∨ (¬ p4347) ∨ (¬ p4366))
    : (¬ p3256) ∨ p2363 ∨ (¬ p2246) ∨ p3527 ∨ (¬ p2608) ∨ (¬ p4341) ∨ (¬ p4133) ∨ (¬ p2744) ∨ (¬ p2331) ∨ p3399 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h52777 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u12)))))))))))))))))))))

theorem step82386 (p2881 p2911 p3051 p3556 p3570 p3741 p4533 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73418 : p3570 ∨ p2881)
    (h41489 : (¬ p2911) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3741) ∨ (¬ p4533))
    : (¬ p2911) ∨ p3051 ∨ p2881 ∨ (¬ p3741) ∨ (¬ p4533) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41489 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step82387 (p2563 p2881 p2911 p3570 p3741 p4110 p4558 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73516 : p4110 ∨ p2563)
    (h51034 : (¬ p2911) ∨ (¬ p3570) ∨ (¬ p3741) ∨ (¬ p4110) ∨ (¬ p4558))
    : (¬ p3741) ∨ (¬ p2911) ∨ p2881 ∨ (¬ p4558) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3741 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51034 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step82389 (p2230 p2427 p2589 p2881 p2911 p3570 p4235 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73284 : p2589 ∨ p2230)
    (h73418 : p3570 ∨ p2881)
    (h44281 : (¬ p2589) ∨ (¬ p2911) ∨ (¬ p3570) ∨ (¬ p4235))
    : (¬ p2911) ∨ p2427 ∨ p2230 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44281 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step82390 (p2881 p2911 p2982 p3570 p3741 p4204 p4948 p5043 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h73418 : p3570 ∨ p2881)
    (h41953 : (¬ p2911) ∨ (¬ p3570) ∨ (¬ p3741) ∨ (¬ p4204) ∨ (¬ p4948) ∨ (¬ p5043))
    : (¬ p2911) ∨ p2982 ∨ (¬ p5043) ∨ (¬ p4204) ∨ (¬ p3741) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41953 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step82391 (p2177 p2299 p2911 p2922 p3379 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h45312 : (¬ p2299) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379))
    : (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45312 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step82392 (p2881 p2911 p2922 p3379 p3570 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h42841 : (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3570))
    : (¬ p2911) ∨ (¬ p2922) ∨ p2881 ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42841 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step82395 (p2437 p2651 p2881 p2911 p3570 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h43203 : (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2911) ∨ (¬ p3570))
    : (¬ p2437) ∨ (¬ p2911) ∨ p2881 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43203 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step82396 (p2177 p2299 p2911 p3367 p3389 p3759 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h46116 : (¬ p2299) ∨ (¬ p2911) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3759))
    : (¬ p2911) ∨ (¬ p3389) ∨ p2177 ∨ (¬ p3759) ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46116 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step82397 (p2406 p2459 p2911 p2922 p3238 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h53676 : (¬ p2459) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3238))
    : (¬ p2911) ∨ (¬ p2922) ∨ p2406 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h53676 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step82398 (p2177 p2299 p2437 p2440 p2911 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h45869 : (¬ p2299) ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2911))
    : (¬ p2437) ∨ (¬ p2911) ∨ p2177 ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45869 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step82400 (p2881 p2911 p3570 p4001 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h20262 : (¬ p2911) ∨ (¬ p3570) ∨ (¬ p4001))
    : (¬ p2911) ∨ (¬ p4001) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20262 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step82403 (p2363 p2459 p2911 p3955 p4347 p4712 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h49633 : (¬ p2459) ∨ (¬ p2911) ∨ (¬ p3955) ∨ (¬ p4347) ∨ (¬ p4712))
    : (¬ p2911) ∨ p2363 ∨ (¬ p4712) ∨ (¬ p2459) ∨ (¬ p3955) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h49633 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step82404 (p2088 p2459 p2911 p3857 p3961 p5199 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h56343 : (¬ p2459) ∨ (¬ p2911) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p5199))
    : (¬ p2911) ∨ (¬ p3961) ∨ p2088 ∨ (¬ p2459) ∨ (¬ p5199) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3961 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5199 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h56343 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step82406 (p2459 p2911 p3146 p3692 p3955 p4441 p4712 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h49384 : (¬ p2459) ∨ (¬ p2911) ∨ (¬ p3692) ∨ (¬ p3955) ∨ (¬ p4441) ∨ (¬ p4712))
    : (¬ p4441) ∨ (¬ p2911) ∨ (¬ p4712) ∨ (¬ p3955) ∨ (¬ p2459) ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4441 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h49384 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step82407 (p2459 p2911 p3146 p3692 p4119 p4647 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h62329 : (¬ p2459) ∨ (¬ p2911) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4647))
    : (¬ p2911) ∨ p3146 ∨ (¬ p4119) ∨ (¬ p2459) ∨ (¬ p4647) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h62329 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step82410 (p2156 p2881 p2911 p3051 p3556 p3570 p3741 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73418 : p3570 ∨ p2881)
    (h44226 : (¬ p2156) ∨ (¬ p2911) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3741))
    : (¬ p2911) ∨ p3051 ∨ p2881 ∨ (¬ p2156) ∨ (¬ p3741) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44226 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step82411 (p2881 p2911 p3125 p3570 p3921 p4204 p4624 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h49656 : (¬ p2911) ∨ (¬ p3125) ∨ (¬ p3570) ∨ (¬ p3921) ∨ (¬ p4204) ∨ (¬ p4624))
    : (¬ p2911) ∨ (¬ p3125) ∨ (¬ p4624) ∨ (¬ p4204) ∨ (¬ p3921) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4624 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h49656 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step82414 (p2177 p2299 p2911 p3921 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h19838 : (¬ p2299) ∨ (¬ p2911) ∨ (¬ p3921))
    : (¬ p2911) ∨ (¬ p3921) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h19838 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step82423 (p2230 p2274 p2563 p2589 p2662 p2727 p3097 p4110 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73352 : p3097 ∨ p2274)
    (h73284 : p2589 ∨ p2230)
    (h73516 : p4110 ∨ p2563)
    (h43046 : (¬ p2589) ∨ (¬ p2662) ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4111))
    : p2727 ∨ (¬ p2662) ∨ p2274 ∨ p2230 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43046 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (False.elim (r3 u5)))))))))))

end ElevenRUP
