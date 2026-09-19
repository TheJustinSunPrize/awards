import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step90199 (p2156 p2187 p2352 p2590 p3956 p4539 : Prop)
    (h73500 : p3956 ∨ p2352)
    (h62573 : (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2590) ∨ (¬ p3956) ∨ (¬ p4539))
    : (¬ p2187) ∨ p2352 ∨ (¬ p2590) ∨ (¬ p4539) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2352) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4539 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h62573 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step90202 (p3483 p3564 p4137 p4342 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h20441 : (¬ p3483) ∨ (¬ p4137) ∨ (¬ p4342))
    : (¬ p3483) ∨ p3564 ∨ (¬ p4342) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4342 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h20441 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step90205 (p3201 p3483 p3654 p3876 p3946 p4031 p4198 p4375 p4644 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73492 : p3946 ∨ p3654)
    (h51244 : (¬ p3483) ∨ (¬ p3876) ∨ (¬ p3946) ∨ (¬ p4031) ∨ (¬ p4198) ∨ (¬ p4375) ∨ (¬ p4644))
    : (¬ p3483) ∨ (¬ p4031) ∨ p3201 ∨ (¬ p4375) ∨ p3654 ∨ (¬ p4198) ∨ (¬ p4644) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51244 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step90206 (p2352 p2598 p3483 p3564 p4137 p4375 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h46419 : (¬ p2352) ∨ (¬ p2598) ∨ (¬ p3483) ∨ (¬ p4137) ∨ (¬ p4375))
    : (¬ p2598) ∨ p3564 ∨ (¬ p3483) ∨ (¬ p2352) ∨ (¬ p4375) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46419 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step90207 (p3125 p3483 p3744 p4428 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h39073 : (¬ p3483) ∨ (¬ p3744) ∨ (¬ p4428))
    : (¬ p3483) ∨ p3125 ∨ (¬ p4428) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4428 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h39073 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step90210 (p2819 p3146 p3483 p3692 p4358 p4433 p4460 p5379 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73564 : p4358 ∨ p2819)
    (h49110 : (¬ p3483) ∨ (¬ p3692) ∨ (¬ p4358) ∨ (¬ p4433) ∨ (¬ p4460) ∨ (¬ p5379))
    : (¬ p3483) ∨ p3146 ∨ p2819 ∨ (¬ p4460) ∨ (¬ p5379) ∨ (¬ p4433) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4460 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h49110 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step90211 (p2122 p2177 p2299 p3483 p3654 p3822 p3946 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73492 : p3946 ∨ p3654)
    (h73234 : p2299 ∨ p2177)
    (h45150 : (¬ p2299) ∨ (¬ p3483) ∨ (¬ p3822) ∨ (¬ p3946))
    : (¬ p3483) ∨ p2122 ∨ p3654 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45150 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step90215 (p2459 p2608 p2829 p2911 p3389 p3483 p3540 p3644 p4330 p4348 p5193 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73402 : p3540 ∨ p3389)
    (h73434 : p3644 ∨ p2911)
    (h64053 : (¬ p2608) ∨ (¬ p2829) ∨ (¬ p3483) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p5193))
    : (¬ p3483) ∨ (¬ p2829) ∨ p2459 ∨ (¬ p2608) ∨ (¬ p4330) ∨ p3389 ∨ p2911 ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h64053 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step90218 (p2122 p3483 p3822 p4025 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h31898 : (¬ p3483) ∨ (¬ p3822) ∨ (¬ p4025))
    : (¬ p3483) ∨ (¬ p4025) ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4025 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h31898 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step90219 (p2122 p2573 p2579 p3483 p3564 p3822 p4108 p4137 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h73274 : p2579 ∨ p2573)
    (h73472 : p3822 ∨ p2122)
    (h56503 : (¬ p2579) ∨ (¬ p3483) ∨ (¬ p3822) ∨ (¬ p4108) ∨ (¬ p4137))
    : (¬ p3483) ∨ p3564 ∨ (¬ p4108) ∨ p2573 ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56503 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step90221 (p2122 p2315 p3483 p3516 p3821 p3822 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73470 : p3821 ∨ p3516)
    (h66009 : (¬ p3483) ∨ (¬ p2315) ∨ (¬ p3821) ∨ (¬ p3822) ∨ p2122)
    : (¬ p3483) ∨ p2122 ∨ (¬ p2315) ∨ p3516 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h66009 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (u1 r3)))))))))))

theorem step90222 (p2248 p2819 p2881 p2901 p2946 p3483 p3654 p3946 p4358 p4503 p5015 : Prop)
    (h73492 : p3946 ∨ p3654)
    (h73564 : p4358 ∨ p2819)
    (h57361 : (¬ p2248) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3483) ∨ (¬ p3946) ∨ (¬ p4358) ∨ (¬ p4503) ∨ (¬ p5015))
    : (¬ p3483) ∨ p3654 ∨ p2819 ∨ (¬ p4503) ∨ (¬ p5015) ∨ (¬ p2901) ∨ (¬ p2248) ∨ (¬ p2946) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3654) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5015 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h57361 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step90226 (p2252 p2437 p2651 p2657 p2750 p2753 p2774 p3461 p3483 p3742 p4831 p5503 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73288 : p2657 ∨ p2651)
    (h50996 : (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3461) ∨ (¬ p3483) ∨ (¬ p3742) ∨ (¬ p4831) ∨ (¬ p5503))
    : (¬ p5503) ∨ (¬ p3483) ∨ (¬ p3461) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2774) ∨ p2437 ∨ (¬ p2753) ∨ (¬ p4831) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5503 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h50996 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step90233 (p2819 p3266 p3461 p3483 p4358 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73564 : p4358 ∨ p2819)
    (h53458 : (¬ p3461) ∨ (¬ p3483) ∨ (¬ p4358) ∨ (¬ p4444))
    : p3266 ∨ (¬ p3483) ∨ (¬ p3461) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53458 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90234 (p2819 p3483 p4345 p4358 p5118 p5580 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h50994 : (¬ p3483) ∨ (¬ p4345) ∨ (¬ p4358) ∨ (¬ p5118) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p3483) ∨ (¬ p4345) ∨ p2819 ∨ (¬ p5118) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4345 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50994 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step90235 (p2230 p2373 p2589 p2608 p2829 p3146 p3483 p3692 p3880 p4330 p5193 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73490 : p3880 ∨ p2373)
    (h73284 : p2589 ∨ p2230)
    (h59221 : (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2829) ∨ (¬ p3483) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4330) ∨ (¬ p5193))
    : (¬ p3483) ∨ p3146 ∨ (¬ p5193) ∨ (¬ p2829) ∨ p2373 ∨ (¬ p2608) ∨ (¬ p4330) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h59221 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step90236 (p2122 p2315 p3483 p3516 p3821 p3822 p4623 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73472 : p3822 ∨ p2122)
    (h48783 : (¬ p2315) ∨ (¬ p3483) ∨ (¬ p3821) ∨ (¬ p3822) ∨ (¬ p4623))
    : (¬ p3483) ∨ (¬ p4623) ∨ p3516 ∨ (¬ p2315) ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4623 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48783 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step90237 (p2641 p2667 p2819 p3483 p3654 p3946 p4154 p4358 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73564 : p4358 ∨ p2819)
    (h73492 : p3946 ∨ p3654)
    (h46614 : (¬ p2667) ∨ (¬ p3483) ∨ (¬ p3946) ∨ (¬ p4154) ∨ (¬ p4358))
    : (¬ p3483) ∨ p2641 ∨ p2819 ∨ (¬ p2667) ∨ p3654 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46614 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step90242 (p2088 p2819 p3483 p3857 p3858 p4345 p4358 p4995 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h73564 : p4358 ∨ p2819)
    (h58817 : (¬ p3483) ∨ (¬ p3857) ∨ (¬ p3858) ∨ (¬ p4345) ∨ (¬ p4358) ∨ (¬ p4995))
    : (¬ p3483) ∨ p2088 ∨ (¬ p3858) ∨ (¬ p4995) ∨ (¬ p4345) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2088) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3858 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4345 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h58817 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step90243 (p2573 p2579 p2819 p3483 p3564 p3905 p4137 p4358 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h73274 : p2579 ∨ p2573)
    (h73564 : p4358 ∨ p2819)
    (h54417 : (¬ p2579) ∨ (¬ p3483) ∨ (¬ p3905) ∨ (¬ p4137) ∨ (¬ p4358))
    : (¬ p3483) ∨ p3564 ∨ p2573 ∨ (¬ p3905) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54417 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step90245 (p2122 p3461 p3483 p3707 p3822 p4321 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h73472 : p3822 ∨ p2122)
    (h58594 : (¬ p3461) ∨ (¬ p3483) ∨ (¬ p3822) ∨ (¬ p4321))
    : p3707 ∨ (¬ p3483) ∨ p2122 ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h58594 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90246 (p2122 p3440 p3461 p3483 p3707 p3822 p4321 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h73472 : p3822 ∨ p2122)
    (h47524 : (¬ p3440) ∨ (¬ p3461) ∨ (¬ p3483) ∨ (¬ p3822) ∨ (¬ p4321))
    : p3707 ∨ (¬ p3483) ∨ (¬ p3461) ∨ p2122 ∨ (¬ p3440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47524 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step90247 (p2187 p2829 p3125 p3483 p3744 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h58033 : (¬ p2187) ∨ (¬ p2829) ∨ (¬ p3483) ∨ (¬ p3744))
    : p3125 ∨ (¬ p3483) ∨ (¬ p2829) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3125) := (fun h => hn (Or.inl h));
    let u1 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h58033 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90248 (p2819 p3063 p3093 p3483 p4358 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h43570 : (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3483) ∨ (¬ p4358))
    : (¬ p3063) ∨ (¬ p3483) ∨ (¬ p3093) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43570 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90250 (p2563 p2819 p3323 p3483 p3986 p4037 p4110 p4358 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73516 : p4110 ∨ p2563)
    (h73564 : p4358 ∨ p2819)
    (h58008 : (¬ p3483) ∨ (¬ p3986) ∨ (¬ p4037) ∨ (¬ p4110) ∨ (¬ p4358))
    : (¬ p3483) ∨ p3323 ∨ (¬ p3986) ∨ p2563 ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h58008 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step90251 (p2122 p2449 p3483 p3822 p3947 p5299 p5379 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73494 : p3947 ∨ p2449)
    (h71840 : (¬ p5299) ∨ (¬ p5379) ∨ (¬ p3483) ∨ (¬ p3822) ∨ (¬ p3947))
    : (¬ p5299) ∨ (¬ p3483) ∨ p2122 ∨ p2449 ∨ (¬ p5379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71840 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step90253 (p2122 p2274 p3461 p3483 p3822 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h44985 : (¬ p2274) ∨ (¬ p3461) ∨ (¬ p3483) ∨ (¬ p3822))
    : (¬ p3483) ∨ p2122 ∨ (¬ p2274) ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h44985 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90258 (p3016 p3343 p3359 p3483 p4022 p5225 : Prop)
    (h73388 : p3359 ∨ p3343)
    (h55236 : (¬ p3016) ∨ (¬ p3359) ∨ (¬ p3483) ∨ (¬ p4022) ∨ (¬ p5225))
    : p3343 ∨ (¬ p3483) ∨ (¬ p4022) ∨ (¬ p3016) ∨ (¬ p5225) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4022 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5225 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h55236 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step90263 (p2598 p2946 p2952 p3055 p3156 p3276 p3361 p3497 p3619 p4749 p5123 p5164 p5568 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h73350 : p3055 ∨ p2598)
    (h73330 : p2952 ∨ p2946)
    (h53369 : (¬ p2952) ∨ (¬ p3055) ∨ (¬ p3276) ∨ (¬ p3361) ∨ (¬ p3497) ∨ (¬ p3619) ∨ (¬ p4749) ∨ (¬ p5123) ∨ (¬ p5164) ∨ (¬ p5568))
    : (¬ p5568) ∨ (¬ p3619) ∨ p3156 ∨ p2598 ∨ (¬ p3276) ∨ (¬ p5164) ∨ (¬ p5123) ∨ (¬ p3361) ∨ (¬ p4749) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5568 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5164 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h53369 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step90265 (p2608 p2737 p3379 p3452 p3590 p4749 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h51216 : (¬ p2608) ∨ (¬ p2737) ∨ (¬ p3452) ∨ (¬ p3590) ∨ (¬ p4749))
    : (¬ p2608) ∨ p3379 ∨ (¬ p3590) ∨ (¬ p2737) ∨ (¬ p4749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h51216 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step90269 (p2230 p2406 p2737 p3238 p3759 p4257 p4749 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h48020 : (¬ p2230) ∨ (¬ p2737) ∨ (¬ p3238) ∨ (¬ p3759) ∨ (¬ p4257) ∨ (¬ p4749))
    : (¬ p2737) ∨ p2406 ∨ (¬ p4749) ∨ (¬ p2230) ∨ (¬ p4257) ∨ (¬ p3759) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2406) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h48020 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step90270 (p2598 p3055 p3434 p3516 p3819 p4324 p4357 p4749 : Prop)
    (h73556 : p4324 ∨ p3434)
    (h73350 : p3055 ∨ p2598)
    (h54787 : (¬ p3055) ∨ (¬ p3516) ∨ (¬ p3819) ∨ (¬ p4324) ∨ (¬ p4357) ∨ (¬ p4749))
    : p3434 ∨ (¬ p3516) ∨ p2598 ∨ (¬ p4357) ∨ (¬ p4749) ∨ (¬ p3819) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4357 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h54787 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step90272 (p2383 p2387 p2630 p2668 p2785 p4841 p4972 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h42143 : (¬ p2387) ∨ (¬ p2630) ∨ (¬ p2668) ∨ (¬ p2785) ∨ (¬ p4841) ∨ (¬ p4972))
    : (¬ p4841) ∨ (¬ p2668) ∨ (¬ p4972) ∨ p2383 ∨ (¬ p2630) ∨ (¬ p2785) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4841 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42143 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step90277 (p2505 p3136 p3319 p3917 p4116 p4704 p4841 : Prop)
    (h73046 : p4704)
    (h52019 : (¬ p2505) ∨ (¬ p3136) ∨ (¬ p3319) ∨ (¬ p3917) ∨ (¬ p4116) ∨ (¬ p4704) ∨ (¬ p4841))
    : (¬ p3917) ∨ (¬ p3319) ∨ (¬ p4116) ∨ (¬ p3136) ∨ (¬ p2505) ∨ (¬ p4841) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3917 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4841 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4704 := h73046;
    (Or.elim h52019 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step90280 (p2630 p2668 p2819 p4358 p4841 p4972 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h52693 : (¬ p2630) ∨ (¬ p2668) ∨ (¬ p4358) ∨ (¬ p4841) ∨ (¬ p4972))
    : (¬ p4841) ∨ (¬ p2668) ∨ (¬ p4972) ∨ p2819 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4841 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h52693 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step90283 (p2122 p2307 p2630 p3567 p3822 p4841 p4972 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h52981 : (¬ p2307) ∨ (¬ p2630) ∨ (¬ p3567) ∨ (¬ p3822) ∨ (¬ p4841) ∨ (¬ p4972))
    : (¬ p4841) ∨ p2122 ∨ (¬ p3567) ∨ (¬ p4972) ∨ (¬ p2307) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4841 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h52981 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step90285 (p2122 p2307 p2630 p2951 p2962 p3822 p4841 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h69676 : (¬ p2307) ∨ (¬ p2951) ∨ (¬ p2962) ∨ (¬ p2630) ∨ (¬ p3822) ∨ (¬ p4841))
    : (¬ p4841) ∨ (¬ p2307) ∨ (¬ p2630) ∨ (¬ p2951) ∨ p2122 ∨ (¬ p2962) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4841 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h69676 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step90286 (p2246 p2331 p2668 p2751 p2819 p4358 p4841 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h41901 : (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p2751) ∨ (¬ p4358) ∨ (¬ p4841))
    : (¬ p4841) ∨ (¬ p2668) ∨ (¬ p2751) ∨ (¬ p2246) ∨ p2819 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4841 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41901 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step90289 (p2122 p2307 p2598 p2786 p3055 p3822 p4749 p4841 : Prop)
    (h73350 : p3055 ∨ p2598)
    (h73472 : p3822 ∨ p2122)
    (h51084 : (¬ p2307) ∨ (¬ p2786) ∨ (¬ p3055) ∨ (¬ p3822) ∨ (¬ p4749) ∨ (¬ p4841))
    : (¬ p4841) ∨ (¬ p2307) ∨ p2598 ∨ (¬ p4749) ∨ p2122 ∨ (¬ p2786) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4841 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51084 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step90290 (p2122 p2132 p2138 p2307 p2786 p3822 p4841 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73214 : p2138 ∨ p2132)
    (h67288 : (¬ p3822) ∨ (¬ p4841) ∨ (¬ p2307) ∨ (¬ p2786) ∨ (¬ p2138))
    : p2122 ∨ (¬ p4841) ∨ p2132 ∨ (¬ p2786) ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p4841 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h67288 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step90293 (p2122 p2295 p2331 p3822 p4790 p4841 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h53138 : (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3822) ∨ (¬ p4790) ∨ (¬ p4841))
    : (¬ p4841) ∨ (¬ p2295) ∨ p2122 ∨ (¬ p4790) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4841 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h53138 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step90294 (p2383 p2641 p2751 p2819 p3567 p4358 p4841 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h42561 : (¬ p2383) ∨ (¬ p2641) ∨ (¬ p2751) ∨ (¬ p3567) ∨ (¬ p4358) ∨ (¬ p4841))
    : (¬ p2383) ∨ (¬ p4841) ∨ (¬ p2641) ∨ p2819 ∨ (¬ p2751) ∨ (¬ p3567) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4841 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42561 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step90296 (p2122 p2608 p2630 p3309 p3822 p4841 p4869 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h45441 : (¬ p2608) ∨ (¬ p2630) ∨ (¬ p3309) ∨ (¬ p3822) ∨ (¬ p4841) ∨ (¬ p4869))
    : p2122 ∨ (¬ p4841) ∨ (¬ p2608) ∨ (¬ p4869) ∨ (¬ p3309) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p4841 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4869 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45441 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step90297 (p2819 p3063 p3367 p3585 p4358 p4749 p4841 p4869 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h73428 : p3585 ∨ p3367)
    (h42126 : (¬ p3063) ∨ (¬ p3585) ∨ (¬ p4358) ∨ (¬ p4749) ∨ (¬ p4841) ∨ (¬ p4869))
    : (¬ p3063) ∨ (¬ p4869) ∨ (¬ p4841) ∨ p2819 ∨ p3367 ∨ (¬ p4749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4869 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4841 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42126 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step90300 (p2122 p2177 p2881 p3570 p4204 p4401 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h63893 : (¬ p2122) ∨ (¬ p2177) ∨ (¬ p3570) ∨ (¬ p4204) ∨ (¬ p4401))
    : (¬ p2122) ∨ p2881 ∨ (¬ p4204) ∨ (¬ p4401) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4401 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h63893 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step90302 (p2122 p2295 p2331 p2963 p3568 p4426 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73338 : p2963 ∨ p2331)
    (h71841 : (¬ p4426) ∨ (¬ p3568) ∨ (¬ p2122) ∨ (¬ p2963))
    : p2295 ∨ p2331 ∨ (¬ p2122) ∨ (¬ p4426) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2295) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71841 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step90306 (p2122 p2553 p2573 p2579 p2588 p4375 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73282 : p2588 ∨ p2553)
    (h71843 : (¬ p2588) ∨ (¬ p2122) ∨ (¬ p2579) ∨ (¬ p4375))
    : (¬ p2122) ∨ p2573 ∨ p2553 ∨ (¬ p4375) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h71843 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step90310 (p2122 p2553 p2588 p2774 p3564 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h47424 : (¬ p2122) ∨ (¬ p2588) ∨ (¬ p2774) ∨ (¬ p3564))
    : (¬ p2122) ∨ p2553 ∨ (¬ p3564) ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47424 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step90314 (p2122 p2553 p2588 p2598 p3055 p3422 p3584 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h73282 : p2588 ∨ p2553)
    (h73350 : p3055 ∨ p2598)
    (h47616 : (¬ p2122) ∨ (¬ p2588) ∨ (¬ p3055) ∨ (¬ p3584))
    : (¬ p2122) ∨ p3422 ∨ p2553 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47616 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90316 (p2122 p2177 p2311 p2341 p2782 p3551 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h41852 : (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2311) ∨ (¬ p2782) ∨ (¬ p3551))
    : p2341 ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2782) ∨ (¬ p2311) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2782 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41852 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step90318 (p2122 p2307 p2313 p2785 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h6273 : (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2785))
    : p2307 ∨ (¬ p2122) ∨ (¬ p2785) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2307) := (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h6273 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step90319 (p2122 p2352 p2553 p2588 p2774 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h45001 : (¬ p2122) ∨ (¬ p2352) ∨ (¬ p2588) ∨ (¬ p2774))
    : (¬ p2122) ∨ p2553 ∨ (¬ p2352) ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45001 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step90326 (p2122 p2187 p2274 p2829 p3097 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h58539 : (¬ p2122) ∨ (¬ p2187) ∨ (¬ p2829) ∨ (¬ p3097))
    : (¬ p2122) ∨ (¬ p2829) ∨ p2274 ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h58539 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90328 (p2122 p2187 p2274 p2774 p3097 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h45000 : (¬ p2122) ∨ (¬ p2187) ∨ (¬ p2774) ∨ (¬ p3097))
    : (¬ p2122) ∨ (¬ p2774) ∨ (¬ p2187) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45000 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90329 (p2122 p2298 p2331 p2807 p3414 p4846 : Prop)
    (h73392 : p3414 ∨ p2807)
    (h42061 : (¬ p2122) ∨ (¬ p2298) ∨ (¬ p2331) ∨ (¬ p3414) ∨ (¬ p4846))
    : (¬ p2122) ∨ (¬ p2331) ∨ (¬ p2298) ∨ p2807 ∨ (¬ p4846) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2298 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4846 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42061 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step90330 (p2122 p2274 p2383 p2819 p3097 p4358 p4489 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h73352 : p3097 ∨ p2274)
    (h50978 : (¬ p2122) ∨ (¬ p2383) ∨ (¬ p3097) ∨ (¬ p4358) ∨ (¬ p4489))
    : (¬ p2383) ∨ (¬ p2122) ∨ (¬ p4489) ∨ p2819 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4489 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50978 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step90332 (p2122 p2241 p2247 p2307 p2313 p2518 p2744 p2778 p2819 p3366 p3379 p4358 p4596 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73238 : p2313 ∨ p2307)
    (h73564 : p4358 ∨ p2819)
    (h52802 : (¬ p2122) ∨ (¬ p2247) ∨ (¬ p2313) ∨ (¬ p2518) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p3366) ∨ (¬ p3379) ∨ (¬ p4358) ∨ (¬ p4596))
    : (¬ p2122) ∨ p2241 ∨ (¬ p2744) ∨ (¬ p2518) ∨ (¬ p4596) ∨ (¬ p3366) ∨ p2307 ∨ (¬ p2778) ∨ p2819 ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h52802 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step90333 (p2122 p2819 p3093 p3309 p3549 p3591 p4358 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73564 : p4358 ∨ p2819)
    (h73406 : p3549 ∨ p3309)
    (h46207 : (¬ p2122) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4358))
    : (¬ p2122) ∨ p3093 ∨ p2819 ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46207 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step90335 (p2122 p2307 p2313 p2459 p2819 p4138 p4348 p4358 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73238 : p2313 ∨ p2307)
    (h73564 : p4358 ∨ p2819)
    (h47631 : (¬ p2122) ∨ (¬ p2313) ∨ (¬ p4138) ∨ (¬ p4348) ∨ (¬ p4358))
    : (¬ p2122) ∨ p2459 ∨ p2307 ∨ p2819 ∨ (¬ p4138) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47631 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step90337 (p2122 p2312 p2437 p2819 p3016 p3742 p4279 p4358 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h73452 : p3742 ∨ p2437)
    (h47037 : (¬ p2122) ∨ (¬ p2312) ∨ (¬ p3016) ∨ (¬ p3742) ∨ (¬ p4279) ∨ (¬ p4358))
    : (¬ p2122) ∨ (¬ p2312) ∨ (¬ p3016) ∨ (¬ p4279) ∨ p2819 ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4279 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u7 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h47037 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step90338 (p2122 p2230 p2307 p2313 p2440 p2778 p2819 p3083 p4358 p4419 p4596 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73564 : p4358 ∨ p2819)
    (h42334 : (¬ p2122) ∨ (¬ p2230) ∨ (¬ p2313) ∨ (¬ p2440) ∨ (¬ p2778) ∨ (¬ p3083) ∨ (¬ p4358) ∨ (¬ p4419) ∨ (¬ p4596))
    : (¬ p2778) ∨ (¬ p2122) ∨ p2307 ∨ (¬ p4419) ∨ (¬ p3083) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p4596) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2778 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h42334 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step90339 (p2122 p2819 p3063 p3093 p4358 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h45613 : (¬ p2122) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p4358))
    : (¬ p3063) ∨ (¬ p2122) ∨ p2819 ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45613 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90340 (p2122 p2241 p2307 p2313 p2727 p2819 p3083 p4358 p4596 p5021 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73564 : p4358 ∨ p2819)
    (h63608 : (¬ p2122) ∨ (¬ p2241) ∨ (¬ p2313) ∨ (¬ p2727) ∨ (¬ p3083) ∨ (¬ p4358) ∨ (¬ p4596) ∨ (¬ p5021))
    : p2307 ∨ p2819 ∨ (¬ p3083) ∨ (¬ p5021) ∨ (¬ p2727) ∨ (¬ p4596) ∨ (¬ p2241) ∨ (¬ p2122) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2307) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4596 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h63608 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step90342 (p2122 p2177 p2417 p2774 p2922 p2928 p3379 p3452 p4278 p4666 p4733 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73320 : p2928 ∨ p2922)
    (h73546 : p4278 ∨ p2417)
    (h51460 : (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2774) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p4733))
    : (¬ p2122) ∨ p3379 ∨ (¬ p4666) ∨ (¬ p4733) ∨ (¬ p2177) ∨ p2922 ∨ (¬ p2774) ∨ p2417 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h51460 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step90344 (p2122 p2307 p2313 p2383 p2829 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h55042 : (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p2829))
    : (¬ p2122) ∨ (¬ p2383) ∨ p2307 ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h55042 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step90346 (p2122 p2230 p2246 p2307 p2313 p2663 p2744 p3146 p3156 p3204 p3879 p3917 p3953 p4604 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h61320 : (¬ p2122) ∨ (¬ p2230) ∨ (¬ p2246) ∨ (¬ p2313) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3204) ∨ (¬ p3879) ∨ (¬ p3917) ∨ (¬ p3953) ∨ (¬ p4604))
    : (¬ p2246) ∨ (¬ p3146) ∨ (¬ p3156) ∨ p2307 ∨ (¬ p3953) ∨ (¬ p2663) ∨ (¬ p2122) ∨ (¬ p2744) ∨ (¬ p3879) ∨ (¬ p3204) ∨ (¬ p2230) ∨ (¬ p3917) ∨ (¬ p4604) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61320 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u13))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u11))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u4))) (fun r11 => (False.elim (r11 u12)))))))))))))))))))))))))))

theorem step90348 (p2122 p2352 p2553 p2588 p3367 p4375 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h45031 : (¬ p2122) ∨ (¬ p2352) ∨ (¬ p2588) ∨ (¬ p3367) ∨ (¬ p4375))
    : (¬ p3367) ∨ (¬ p2122) ∨ (¬ p2352) ∨ (¬ p4375) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45031 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step90349 (p2122 p2274 p2608 p2829 p3097 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h42773 : (¬ p2122) ∨ (¬ p2608) ∨ (¬ p2829) ∨ (¬ p3097))
    : (¬ p2122) ∨ (¬ p2608) ∨ (¬ p2829) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42773 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90350 (p2122 p2553 p2588 p2608 p2829 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h43780 : (¬ p2122) ∨ (¬ p2588) ∨ (¬ p2608) ∨ (¬ p2829))
    : (¬ p2122) ∨ p2553 ∨ (¬ p2608) ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43780 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step90351 (p2122 p2187 p2230 p2563 p2589 p2608 p2829 p3989 p4110 p5193 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h73502 : p3989 ∨ p2187)
    (h73284 : p2589 ∨ p2230)
    (h71844 : (¬ p2829) ∨ (¬ p2608) ∨ (¬ p5193) ∨ (¬ p2589) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p2122))
    : (¬ p2122) ∨ (¬ p2829) ∨ (¬ p2608) ∨ p2563 ∨ p2187 ∨ p2230 ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h71844 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (False.elim (r5 u0)))))))))))))))

theorem step90353 (p2122 p2274 p2829 p2839 p3097 p3583 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73352 : p3097 ∨ p2274)
    (h45947 : (¬ p2122) ∨ (¬ p2829) ∨ (¬ p3097) ∨ (¬ p3583))
    : (¬ p2829) ∨ p2839 ∨ p2274 ∨ (¬ p2122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45947 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90354 (p2122 p2396 p2406 p2761 p2774 p2982 p3238 p3379 p3452 p4733 p4948 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73846 : p4948 ∨ p2982)
    (h73374 : p3238 ∨ p2406)
    (h51452 : (¬ p2122) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p2774) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4733) ∨ (¬ p4948))
    : p3379 ∨ (¬ p2761) ∨ (¬ p2122) ∨ (¬ p4733) ∨ p2982 ∨ p2406 ∨ (¬ p2774) ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h51452 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u9)))))))))))))))))

theorem step90355 (p2122 p2284 p2307 p2313 p3952 p3985 p4356 p5053 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73496 : p3952 ∨ p2284)
    (h62774 : (¬ p2122) ∨ (¬ p2313) ∨ (¬ p3952) ∨ (¬ p3985) ∨ (¬ p4356) ∨ (¬ p5053))
    : (¬ p2122) ∨ p2307 ∨ p2284 ∨ (¬ p5053) ∨ (¬ p4356) ∨ (¬ p3985) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3985 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h62774 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step90359 (p2122 p2252 p2396 p2528 p2534 p2651 p2657 p2750 p2829 p3083 p3950 p4256 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73268 : p2534 ∨ p2528)
    (h73542 : p4256 ∨ p3083)
    (h53852 : (¬ p2122) ∨ (¬ p2252) ∨ (¬ p2396) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2829) ∨ (¬ p3950) ∨ (¬ p4256))
    : (¬ p2829) ∨ (¬ p2122) ∨ (¬ p2252) ∨ p2651 ∨ (¬ p2396) ∨ (¬ p3950) ∨ (¬ p2750) ∨ p2528 ∨ p3083 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u11 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h53852 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u11)))))))))))))))))))

theorem step90362 (p2122 p2307 p2313 p2373 p2440 p2542 p2651 p2778 p2819 p4358 p4433 p4786 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h73238 : p2313 ∨ p2307)
    (h73270 : p2542 ∨ p2440)
    (h63614 : (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2373) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2778) ∨ (¬ p4358) ∨ (¬ p4433) ∨ (¬ p4786))
    : p2819 ∨ (¬ p2122) ∨ p2307 ∨ (¬ p2651) ∨ (¬ p2373) ∨ (¬ p4786) ∨ p2440 ∨ (¬ p2778) ∨ (¬ p4433) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h63614 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step90363 (p2122 p2553 p2588 p2598 p2774 p3055 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73350 : p3055 ∨ p2598)
    (h52739 : (¬ p2122) ∨ (¬ p2588) ∨ (¬ p2774) ∨ (¬ p3055))
    : (¬ p2122) ∨ p2553 ∨ p2598 ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52739 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step90364 (p2122 p2396 p2437 p2651 p2657 p2774 p2911 p3644 p3742 p4668 p4789 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73288 : p2657 ∨ p2651)
    (h73434 : p3644 ∨ p2911)
    (h63211 : (¬ p2122) ∨ (¬ p2396) ∨ (¬ p2657) ∨ (¬ p2774) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4668) ∨ (¬ p4789))
    : p2437 ∨ p2651 ∨ (¬ p2774) ∨ (¬ p4789) ∨ p2911 ∨ (¬ p2122) ∨ (¬ p2396) ∨ (¬ p4668) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63211 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step90365 (p2122 p2341 p2819 p3575 p4138 p4358 p4712 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h40962 : (¬ p2122) ∨ (¬ p2341) ∨ (¬ p3575) ∨ (¬ p4138) ∨ (¬ p4358) ∨ (¬ p4712))
    : (¬ p2341) ∨ (¬ p3575) ∨ (¬ p4712) ∨ (¬ p2122) ∨ (¬ p4138) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h40962 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step90368 (p2122 p2819 p2881 p4138 p4358 p4559 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h50991 : (¬ p2122) ∨ (¬ p2881) ∨ (¬ p4138) ∨ (¬ p4358) ∨ (¬ p4559))
    : (¬ p2881) ∨ (¬ p2122) ∨ (¬ p4138) ∨ (¬ p4559) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50991 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step90369 (p2088 p2122 p3609 p4078 p4170 p4340 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h71845 : (¬ p4170) ∨ (¬ p4340) ∨ (¬ p4078) ∨ (¬ p2122) ∨ (¬ p2088))
    : p3609 ∨ (¬ p2122) ∨ (¬ p2088) ∨ (¬ p4078) ∨ (¬ p4170) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4078 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h71845 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step90372 (p2122 p2307 p2313 p2778 p2946 p3146 p3156 p3917 p4604 p4786 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h59730 : (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2778) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3917) ∨ (¬ p4604) ∨ (¬ p4786))
    : (¬ p2778) ∨ (¬ p2122) ∨ (¬ p3146) ∨ (¬ p4604) ∨ (¬ p2946) ∨ p2307 ∨ (¬ p3917) ∨ (¬ p3156) ∨ (¬ p4786) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2778 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h59730 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step90374 (p2122 p2307 p2313 p2630 p2667 p2810 p4426 p4975 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73316 : p2810 ∨ p2630)
    (h50659 : (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2667) ∨ (¬ p2810) ∨ (¬ p4426) ∨ (¬ p4975))
    : (¬ p2122) ∨ p2307 ∨ (¬ p2667) ∨ (¬ p4975) ∨ (¬ p4426) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h50659 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step90375 (p2122 p2307 p2313 p2778 p2829 p4734 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h72735 : p4734)
    (h49739 : (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2778) ∨ (¬ p2829) ∨ (¬ p4734))
    : (¬ p2778) ∨ (¬ p2122) ∨ p2307 ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2778 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4734 := h72735;
    (Or.elim h49739 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step90376 (p2122 p2307 p2313 p2696 p2778 p4842 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h42129 : (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2696) ∨ (¬ p2778) ∨ (¬ p4842))
    : (¬ p2778) ∨ p2307 ∨ (¬ p2122) ∨ (¬ p4842) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2778 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42129 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step90378 (p2122 p2307 p2313 p2577 p2662 p3136 p4315 p4426 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73550 : p4315 ∨ p3136)
    (h69677 : (¬ p2122) ∨ (¬ p4315) ∨ (¬ p4426) ∨ (¬ p2662) ∨ (¬ p2577) ∨ (¬ p2313))
    : p2307 ∨ (¬ p2122) ∨ p3136 ∨ (¬ p2662) ∨ (¬ p4426) ∨ (¬ p2577) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2307) := (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h69677 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step90379 (p2122 p2307 p2313 p2383 p2630 p2810 p4426 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73238 : p2313 ∨ p2307)
    (h55526 : (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p2810) ∨ (¬ p4426))
    : (¬ p2383) ∨ (¬ p2122) ∨ p2630 ∨ p2307 ∨ (¬ p4426) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55526 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step90381 (p2122 p2177 p2252 p2417 p2437 p2651 p2657 p2750 p2753 p2774 p3742 p4278 p4666 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73452 : p3742 ∨ p2437)
    (h73546 : p4278 ∨ p2417)
    (h42300 : (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4666))
    : p2651 ∨ p2437 ∨ p2417 ∨ (¬ p2122) ∨ (¬ p4666) ∨ (¬ p2774) ∨ (¬ p2177) ∨ (¬ p2753) ∨ (¬ p2252) ∨ (¬ p2750) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42300 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step90385 (p2122 p2307 p2313 p2363 p2778 p2819 p4347 p4358 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73564 : p4358 ∨ p2819)
    (h73238 : p2313 ∨ p2307)
    (h55907 : (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2778) ∨ (¬ p4347) ∨ (¬ p4358))
    : p2363 ∨ (¬ p2122) ∨ p2819 ∨ (¬ p2778) ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55907 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step90386 (p2122 p2427 p2563 p2819 p4235 p4275 p4358 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h73536 : p4235 ∨ p2427)
    (h47045 : (¬ p2122) ∨ (¬ p2563) ∨ (¬ p4235) ∨ (¬ p4275) ∨ (¬ p4358))
    : (¬ p2122) ∨ p2819 ∨ (¬ p2563) ∨ p2427 ∨ (¬ p4275) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47045 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step90387 (p2122 p2274 p2563 p3097 p4110 p4885 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73516 : p4110 ∨ p2563)
    (h68235 : (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4885) ∨ (¬ p2122))
    : (¬ p2122) ∨ p2274 ∨ (¬ p4885) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h68235 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step90389 (p2122 p2312 p2449 p3516 p3947 p4067 p4846 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h41716 : (¬ p2122) ∨ (¬ p2312) ∨ (¬ p3516) ∨ (¬ p3947) ∨ (¬ p4067) ∨ (¬ p4846))
    : (¬ p3516) ∨ p2449 ∨ (¬ p2312) ∨ (¬ p2122) ∨ (¬ p4846) ∨ (¬ p4067) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4846 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41716 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step90391 (p2122 p2396 p2406 p2563 p2761 p2774 p3238 p3379 p3452 p4110 p4733 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73374 : p3238 ∨ p2406)
    (h73516 : p4110 ∨ p2563)
    (h64211 : (¬ p2122) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p2774) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4110) ∨ (¬ p4733))
    : (¬ p2122) ∨ p3379 ∨ p2406 ∨ (¬ p4733) ∨ (¬ p2774) ∨ (¬ p2761) ∨ (¬ p2396) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64211 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step90392 (p2122 p2246 p2307 p2313 p2528 p2651 p2744 p2778 p3083 p3366 p3917 p4604 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h52873 : (¬ p2122) ∨ (¬ p2246) ∨ (¬ p2313) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p3083) ∨ (¬ p3366) ∨ (¬ p3917) ∨ (¬ p4604))
    : (¬ p2778) ∨ (¬ p2122) ∨ (¬ p2651) ∨ (¬ p3366) ∨ (¬ p4604) ∨ (¬ p3083) ∨ (¬ p2528) ∨ p2307 ∨ (¬ p2744) ∨ (¬ p2246) ∨ (¬ p3917) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2778 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h52873 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (False.elim (r9 u4)))))))))))))))))))))))

theorem step90394 (p2122 p2177 p2245 p2774 p2946 p2952 p3146 p3256 p3661 p4118 p4733 p4905 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h73330 : p2952 ∨ p2946)
    (h50341 : (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2245) ∨ (¬ p2774) ∨ (¬ p2952) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p4733) ∨ (¬ p4905))
    : (¬ p2122) ∨ (¬ p2774) ∨ (¬ p3146) ∨ (¬ p2177) ∨ (¬ p3661) ∨ p3256 ∨ (¬ p2245) ∨ (¬ p4733) ∨ p2946 ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h50341 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step90395 (p2122 p2230 p2373 p2396 p2589 p2774 p3146 p3692 p3880 p3950 p4729 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73284 : p2589 ∨ p2230)
    (h73490 : p3880 ∨ p2373)
    (h56267 : (¬ p2122) ∨ (¬ p2396) ∨ (¬ p2589) ∨ (¬ p2774) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p3950) ∨ (¬ p4729))
    : p3146 ∨ (¬ p2396) ∨ p2230 ∨ p2373 ∨ (¬ p3950) ∨ (¬ p2122) ∨ (¬ p4729) ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56267 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step90397 (p2122 p2230 p2589 p2774 p2982 p3791 p4322 p4729 p4826 p4948 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h73846 : p4948 ∨ p2982)
    (h54923 : (¬ p2122) ∨ (¬ p2589) ∨ (¬ p2774) ∨ (¬ p3791) ∨ (¬ p4322) ∨ (¬ p4729) ∨ (¬ p4826) ∨ (¬ p4948))
    : (¬ p4322) ∨ (¬ p3791) ∨ p2230 ∨ (¬ p4826) ∨ p2982 ∨ (¬ p2122) ∨ (¬ p2774) ∨ (¬ p4729) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54923 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u9)))))))))))))))))

theorem step90401 (p2122 p2143 p2274 p3097 p3985 p4032 p5043 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h54773 : (¬ p2122) ∨ (¬ p2143) ∨ (¬ p3097) ∨ (¬ p3985) ∨ (¬ p4032) ∨ (¬ p5043))
    : (¬ p2122) ∨ p2274 ∨ (¬ p5043) ∨ (¬ p2143) ∨ (¬ p3985) ∨ (¬ p4032) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3985 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h54773 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step90404 (p2122 p2553 p2588 p3016 p3574 p4375 p4753 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73422 : p3574 ∨ p3016)
    (h55260 : (¬ p2122) ∨ (¬ p2588) ∨ (¬ p3574) ∨ (¬ p4375) ∨ (¬ p4753))
    : (¬ p2122) ∨ (¬ p4375) ∨ p2553 ∨ (¬ p4753) ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55260 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step90406 (p2122 p2132 p2274 p2470 p2476 p3016 p3083 p3097 p3574 p3589 p3985 p4718 p5193 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73250 : p2476 ∨ p2470)
    (h73422 : p3574 ∨ p3016)
    (h54713 : (¬ p2122) ∨ (¬ p2132) ∨ (¬ p2476) ∨ (¬ p3083) ∨ (¬ p3097) ∨ (¬ p3574) ∨ (¬ p3589) ∨ (¬ p3985) ∨ (¬ p4718) ∨ (¬ p5193))
    : (¬ p2122) ∨ (¬ p3589) ∨ (¬ p4718) ∨ (¬ p3985) ∨ p2274 ∨ (¬ p3083) ∨ (¬ p5193) ∨ p2470 ∨ p3016 ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3985 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h54713 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step90407 (p2122 p2252 p2750 p2753 p2774 p2946 p2952 p3115 p3791 p4208 p4322 p4826 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h73330 : p2952 ∨ p2946)
    (h64928 : (¬ p2122) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2952) ∨ (¬ p3791) ∨ (¬ p4208) ∨ (¬ p4322) ∨ (¬ p4826))
    : (¬ p3791) ∨ (¬ p2753) ∨ p3115 ∨ (¬ p2122) ∨ (¬ p2252) ∨ p2946 ∨ (¬ p4322) ∨ (¬ p4826) ∨ (¬ p2750) ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3791 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h64928 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step90408 (p2122 p2553 p2588 p2696 p2753 p2839 p3115 p3564 p3583 p4208 p4316 p4368 p4842 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h73424 : p3583 ∨ p2839)
    (h73282 : p2588 ∨ p2553)
    (h42123 : (¬ p2122) ∨ (¬ p2588) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3564) ∨ (¬ p3583) ∨ (¬ p4208) ∨ (¬ p4316) ∨ (¬ p4368) ∨ (¬ p4842))
    : (¬ p3564) ∨ p3115 ∨ (¬ p4316) ∨ (¬ p4368) ∨ (¬ p4842) ∨ p2839 ∨ (¬ p2122) ∨ (¬ p2753) ∨ p2553 ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h42123 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step90410 (p2122 p3093 p3399 p4366 p4427 p4867 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h48825 : (¬ p2122) ∨ (¬ p3093) ∨ (¬ p4366) ∨ (¬ p4427) ∨ (¬ p4867))
    : p3399 ∨ (¬ p4427) ∨ (¬ p4867) ∨ (¬ p3093) ∨ (¬ p2122) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p4427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4867 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48825 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step90411 (p2122 p2177 p2241 p2449 p2750 p2753 p2774 p3032 p3399 p3947 p4366 p4666 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73570 : p4366 ∨ p3399)
    (h63241 : (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3032) ∨ (¬ p3947) ∨ (¬ p4366) ∨ (¬ p4666))
    : (¬ p2753) ∨ (¬ p3032) ∨ p2449 ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2241) ∨ (¬ p2750) ∨ p3399 ∨ (¬ p2774) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2753 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h63241 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step90412 (p2122 p2177 p2753 p2774 p3379 p3399 p3631 p3817 p4366 p4666 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73468 : p3817 ∨ p3631)
    (h71846 : (¬ p3817) ∨ (¬ p2177) ∨ (¬ p2122) ∨ (¬ p2774) ∨ (¬ p4666) ∨ (¬ p4366) ∨ (¬ p2753) ∨ (¬ p3379))
    : (¬ p2753) ∨ (¬ p2122) ∨ p3399 ∨ (¬ p2774) ∨ (¬ p4666) ∨ p3631 ∨ (¬ p3379) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2753 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h71846 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step90414 (p2122 p2241 p2396 p2750 p2753 p2774 p3073 p3449 p3860 p3950 p4261 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h73482 : p3860 ∨ p3449)
    (h63263 : (¬ p2122) ∨ (¬ p2241) ∨ (¬ p2396) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4261))
    : p3073 ∨ (¬ p3950) ∨ (¬ p2774) ∨ (¬ p2396) ∨ (¬ p2241) ∨ p3449 ∨ (¬ p2753) ∨ (¬ p2122) ∨ (¬ p2750) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h63263 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step90416 (p2122 p2774 p3063 p3309 p3549 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h43488 : (¬ p2122) ∨ (¬ p2774) ∨ (¬ p3063) ∨ (¬ p3549))
    : p3309 ∨ (¬ p2774) ∨ (¬ p3063) ∨ (¬ p2122) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3309) := (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h43488 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90418 (p2122 p2177 p2241 p2247 p2774 p2992 p3156 p3497 p3662 p4733 p4905 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73400 : p3497 ∨ p3156)
    (h73440 : p3662 ∨ p2992)
    (h61963 : (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2774) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p4733) ∨ (¬ p4905))
    : (¬ p2122) ∨ p2241 ∨ (¬ p2774) ∨ (¬ p4733) ∨ p3156 ∨ (¬ p2177) ∨ (¬ p4905) ∨ p2992 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h61963 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step90420 (p2122 p2307 p2313 p2778 p2819 p4358 p5580 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73564 : p4358 ∨ p2819)
    (h46935 : (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2778) ∨ (¬ p4358) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p2778) ∨ p2307 ∨ p2819 ∨ (¬ p2122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46935 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step90422 (p2122 p2252 p2396 p2528 p2534 p2651 p2657 p2750 p2753 p2774 p3083 p3950 p4256 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73542 : p4256 ∨ p3083)
    (h73288 : p2657 ∨ p2651)
    (h64521 : (¬ p2122) ∨ (¬ p2252) ∨ (¬ p2396) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3950) ∨ (¬ p4256))
    : (¬ p2753) ∨ p2528 ∨ (¬ p2252) ∨ (¬ p3950) ∨ (¬ p2774) ∨ p3083 ∨ (¬ p2122) ∨ p2651 ∨ (¬ p2396) ∨ (¬ p2750) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2753 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64521 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u11)))))))))))))))))))))

theorem step90424 (p2122 p2598 p3309 p3549 p3953 p4375 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h71849 : (¬ p4375) ∨ (¬ p3953) ∨ (¬ p2122) ∨ (¬ p3549) ∨ (¬ p2598))
    : (¬ p2122) ∨ p3309 ∨ (¬ p4375) ∨ (¬ p3953) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3309) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71849 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step90427 (p2829 p4865 p4866 : Prop)
    (h73798 : p4865 ∨ p2829)
    (h8001 : (¬ p4865) ∨ p4866)
    : p2829 ∨ p4866 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4866) := (fun h => hn (Or.inr h));
    let u2 : p4865 := (Or.elim h73798 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h8001 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step90428 (p2829 p4865 p4867 : Prop)
    (h73798 : p4865 ∨ p2829)
    (h8002 : (¬ p4865) ∨ p4867)
    : p2829 ∨ p4867 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4867) := (fun h => hn (Or.inr h));
    let u2 : p4865 := (Or.elim h73798 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h8002 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step90429 (p2829 p3688 p4889 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h45394 : (¬ p3688) ∨ p4889)
    : p2829 ∨ p4889 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4889) := (fun h => hn (Or.inr h));
    let u2 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45394 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step90430 (p2122 p2274 p2608 p2829 p3688 p3822 p3954 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73498 : p3954 ∨ p2608)
    (h73472 : p3822 ∨ p2122)
    (h61829 : (¬ p2274) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p3954))
    : p2829 ∨ p2608 ∨ (¬ p2274) ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61829 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step90432 (p2122 p2187 p2230 p2563 p2608 p2829 p3688 p3822 p3954 p4405 p5190 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73498 : p3954 ∨ p2608)
    (h73444 : p3688 ∨ p2829)
    (h48159 : (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p3954) ∨ (¬ p4405) ∨ (¬ p5190))
    : p2122 ∨ (¬ p2187) ∨ (¬ p5190) ∨ p2608 ∨ (¬ p2230) ∨ (¬ p4405) ∨ p2829 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h48159 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step90437 (p2177 p2311 p2341 p2737 p2785 p2829 p3551 p3688 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73444 : p3688 ∨ p2829)
    (h45278 : (¬ p2177) ∨ (¬ p2311) ∨ (¬ p2737) ∨ (¬ p2785) ∨ (¬ p3551) ∨ (¬ p3688))
    : p2341 ∨ p2829 ∨ (¬ p2177) ∨ (¬ p2737) ∨ (¬ p2785) ∨ (¬ p2311) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45278 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step90438 (p2177 p2299 p2307 p2313 p2737 p2785 p2829 p3688 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73444 : p3688 ∨ p2829)
    (h73234 : p2299 ∨ p2177)
    (h55086 : (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2737) ∨ (¬ p2785) ∨ (¬ p3688))
    : p2307 ∨ p2829 ∨ (¬ p2737) ∨ (¬ p2785) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2307) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55086 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step90439 (p2598 p2774 p2829 p2839 p3055 p3688 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73350 : p3055 ∨ p2598)
    (h45271 : (¬ p2774) ∨ (¬ p2839) ∨ (¬ p3055) ∨ (¬ p3688))
    : p2829 ∨ (¬ p2839) ∨ (¬ p2774) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45271 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90443 (p2829 p3016 p3367 p3688 p4342 p4750 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h59243 : (¬ p3016) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p4342) ∨ (¬ p4750))
    : p2829 ∨ (¬ p3367) ∨ (¬ p4342) ∨ (¬ p3016) ∨ (¬ p4750) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4342 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h59243 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step90444 (p2573 p2829 p3367 p3688 p4342 p4730 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h41027 : (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p4342) ∨ (¬ p4730))
    : (¬ p4342) ∨ p2829 ∨ (¬ p3367) ∨ (¬ p2573) ∨ (¬ p4730) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4342 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41027 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step90446 (p2295 p2307 p2313 p2737 p2785 p2829 p3688 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73444 : p3688 ∨ p2829)
    (h56182 : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2737) ∨ (¬ p2785) ∨ (¬ p3688))
    : p2307 ∨ (¬ p2295) ∨ p2829 ∨ (¬ p2737) ∨ (¬ p2785) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2307) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h56182 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step90448 (p2177 p2299 p2307 p2313 p2459 p2785 p2829 p3688 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73234 : p2299 ∨ p2177)
    (h73444 : p3688 ∨ p2829)
    (h73238 : p2313 ∨ p2307)
    (h43869 : (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2785) ∨ (¬ p3688) ∨ (¬ p4348))
    : p2459 ∨ p2177 ∨ (¬ p2785) ∨ p2829 ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2177) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43869 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step90450 (p2177 p2299 p2307 p2313 p2373 p2406 p2598 p2785 p2829 p3590 p3688 p4902 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h73238 : p2313 ∨ p2307)
    (h73444 : p3688 ∨ p2829)
    (h71851 : (¬ p3590) ∨ (¬ p3688) ∨ (¬ p2313) ∨ (¬ p4902) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p2598) ∨ (¬ p2785) ∨ (¬ p2299))
    : (¬ p2373) ∨ (¬ p2785) ∨ p2177 ∨ p2307 ∨ (¬ p3590) ∨ (¬ p4902) ∨ (¬ p2406) ∨ p2829 ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h71851 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step90452 (p2737 p2785 p2829 p3461 p3654 p3688 p3946 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73492 : p3946 ∨ p3654)
    (h73444 : p3688 ∨ p2829)
    (h59180 : (¬ p2737) ∨ (¬ p2785) ∨ (¬ p3688) ∨ (¬ p3946) ∨ (¬ p4191))
    : p3461 ∨ p3654 ∨ (¬ p2785) ∨ p2829 ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3654) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h59180 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step90454 (p2248 p2264 p2459 p2608 p2807 p2829 p3688 p3917 p3954 p4604 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73498 : p3954 ∨ p2608)
    (h48846 : (¬ p2248) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2807) ∨ (¬ p3688) ∨ (¬ p3917) ∨ (¬ p3954) ∨ (¬ p4604))
    : p2829 ∨ p2608 ∨ (¬ p3917) ∨ (¬ p2248) ∨ (¬ p2264) ∨ (¬ p4604) ∨ (¬ p2459) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h48846 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step90455 (p2341 p2608 p2829 p2881 p3246 p3570 p3688 p3917 p3954 p4521 p4625 p4988 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73498 : p3954 ∨ p2608)
    (h73418 : p3570 ∨ p2881)
    (h42419 : (¬ p2341) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3688) ∨ (¬ p3917) ∨ (¬ p3954) ∨ (¬ p4521) ∨ (¬ p4625) ∨ (¬ p4988))
    : (¬ p3246) ∨ p2829 ∨ (¬ p2341) ∨ p2608 ∨ (¬ p4521) ∨ p2881 ∨ (¬ p4625) ∨ (¬ p4988) ∨ (¬ p3917) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h42419 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step90458 (p2122 p2177 p2299 p2737 p2829 p3688 p3822 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73472 : p3822 ∨ p2122)
    (h73234 : p2299 ∨ p2177)
    (h55085 : (¬ p2299) ∨ (¬ p2737) ∨ (¬ p3688) ∨ (¬ p3822))
    : p2829 ∨ p2122 ∨ p2177 ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h55085 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step90459 (p2122 p2177 p2299 p2608 p2829 p3688 p3822 p3954 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73498 : p3954 ∨ p2608)
    (h73472 : p3822 ∨ p2122)
    (h73234 : p2299 ∨ p2177)
    (h45136 : (¬ p2299) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p3954))
    : p2829 ∨ p2608 ∨ p2122 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45136 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step90460 (p2352 p2707 p2829 p3688 p3956 p4342 p4475 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73500 : p3956 ∨ p2352)
    (h71853 : (¬ p3688) ∨ (¬ p3956) ∨ (¬ p2707) ∨ (¬ p4475) ∨ (¬ p4342))
    : p2829 ∨ (¬ p2707) ∨ (¬ p4475) ∨ p2352 ∨ (¬ p4342) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4342 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71853 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step90461 (p2363 p2383 p2387 p2785 p2829 p3266 p3688 p4347 p4444 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73560 : p4347 ∨ p2363)
    (h73246 : p2387 ∨ p2383)
    (h73580 : p4444 ∨ p3266)
    (h42942 : (¬ p2387) ∨ (¬ p2785) ∨ (¬ p3688) ∨ (¬ p4347) ∨ (¬ p4444))
    : p2829 ∨ p2363 ∨ (¬ p2785) ∨ p2383 ∨ p3266 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42942 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u8)))))))))))

theorem step90463 (p2363 p2383 p2387 p2459 p2785 p2829 p3688 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73246 : p2387 ∨ p2383)
    (h73444 : p3688 ∨ p2829)
    (h43317 : (¬ p2387) ∨ (¬ p2459) ∨ (¬ p2785) ∨ (¬ p3688) ∨ (¬ p4347))
    : p2363 ∨ p2383 ∨ (¬ p2459) ∨ p2829 ∨ (¬ p2785) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2383) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43317 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step90464 (p2363 p2383 p2387 p2737 p2785 p2829 p3688 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73444 : p3688 ∨ p2829)
    (h73246 : p2387 ∨ p2383)
    (h58533 : (¬ p2387) ∨ (¬ p2737) ∨ (¬ p2785) ∨ (¬ p3688) ∨ (¬ p4347))
    : p2363 ∨ p2829 ∨ (¬ p2785) ∨ p2383 ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h58533 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step90467 (p2363 p2668 p2737 p2829 p3324 p3688 p4337 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73444 : p3688 ∨ p2829)
    (h73386 : p3324 ∨ p2668)
    (h57281 : (¬ p2737) ∨ (¬ p3324) ∨ (¬ p3688) ∨ (¬ p4337) ∨ (¬ p4347))
    : (¬ p4337) ∨ p2363 ∨ p2829 ∨ p2668 ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4337 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h57281 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step90468 (p2363 p2668 p2737 p2785 p2829 p3324 p3567 p3688 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73444 : p3688 ∨ p2829)
    (h73386 : p3324 ∨ p2668)
    (h42797 : (¬ p2737) ∨ (¬ p2785) ∨ (¬ p3324) ∨ (¬ p3567) ∨ (¬ p3688) ∨ (¬ p4347))
    : p2363 ∨ p2829 ∨ p2668 ∨ (¬ p2737) ∨ (¬ p2785) ∨ (¬ p3567) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42797 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step90469 (p2248 p2331 p2608 p2829 p3688 p3954 p4337 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73498 : p3954 ∨ p2608)
    (h51450 : (¬ p2248) ∨ (¬ p2331) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4337))
    : p2829 ∨ p2608 ∨ (¬ p2331) ∨ (¬ p4337) ∨ (¬ p2248) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4337 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h51450 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step90470 (p2248 p2437 p2608 p2651 p2819 p2829 p2911 p3688 p3954 p4358 p4503 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73564 : p4358 ∨ p2819)
    (h73498 : p3954 ∨ p2608)
    (h61558 : (¬ p2248) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2911) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4358) ∨ (¬ p4503))
    : p2829 ∨ p2819 ∨ (¬ p2651) ∨ p2608 ∨ (¬ p2911) ∨ (¬ p4503) ∨ (¬ p2248) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61558 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step90471 (p2122 p2248 p2352 p2608 p2651 p2829 p3016 p3688 p3822 p3954 p4405 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73444 : p3688 ∨ p2829)
    (h73498 : p3954 ∨ p2608)
    (h62552 : (¬ p2248) ∨ (¬ p2352) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p3954) ∨ (¬ p4405))
    : p2122 ∨ (¬ p2651) ∨ (¬ p2248) ∨ (¬ p3016) ∨ (¬ p4405) ∨ p2829 ∨ p2608 ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h62552 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step90472 (p2241 p2247 p2744 p2774 p2829 p3589 p3688 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73226 : p2247 ∨ p2241)
    (h52716 : (¬ p2247) ∨ (¬ p2744) ∨ (¬ p2774) ∨ (¬ p3589) ∨ (¬ p3688))
    : p2829 ∨ (¬ p3589) ∨ p2241 ∨ (¬ p2774) ∨ (¬ p2744) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52716 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step90476 (p2749 p2829 p2946 p2952 p2992 p3361 p3688 p4842 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73444 : p3688 ∨ p2829)
    (h41472 : (¬ p2749) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3361) ∨ (¬ p3688) ∨ (¬ p4842))
    : (¬ p2992) ∨ p2946 ∨ (¬ p4842) ∨ (¬ p3361) ∨ (¬ p2749) ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41472 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step90477 (p2241 p2608 p2748 p2829 p3688 p3954 p4842 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73444 : p3688 ∨ p2829)
    (h49201 : (¬ p2241) ∨ (¬ p2748) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4842))
    : p2608 ∨ p2829 ∨ (¬ p2748) ∨ (¬ p4842) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h49201 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step90481 (p2406 p2774 p2829 p2850 p3364 p3541 p3684 p3688 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73442 : p3684 ∨ p2850)
    (h56631 : (¬ p2406) ∨ (¬ p2774) ∨ (¬ p3364) ∨ (¬ p3541) ∨ (¬ p3684) ∨ (¬ p3688))
    : p2829 ∨ (¬ p3364) ∨ (¬ p2406) ∨ (¬ p2774) ∨ (¬ p3541) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h56631 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step90483 (p2307 p2313 p2396 p2785 p2829 p3367 p3688 p4107 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73514 : p4107 ∨ p2396)
    (h73238 : p2313 ∨ p2307)
    (h45325 : (¬ p2313) ∨ (¬ p2785) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p4107))
    : p2829 ∨ (¬ p3367) ∨ p2396 ∨ (¬ p2785) ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45325 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step90484 (p2737 p2785 p2829 p3323 p3654 p3688 p3946 : Prop)
    (h73492 : p3946 ∨ p3654)
    (h73444 : p3688 ∨ p2829)
    (h56175 : (¬ p2737) ∨ (¬ p2785) ∨ (¬ p3323) ∨ (¬ p3688) ∨ (¬ p3946))
    : (¬ p3323) ∨ p3654 ∨ p2829 ∨ (¬ p2785) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3654) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h56175 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step90487 (p2459 p2608 p2829 p2911 p3389 p3688 p3917 p3954 p4604 p5190 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73498 : p3954 ∨ p2608)
    (h42234 : (¬ p2459) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3688) ∨ (¬ p3917) ∨ (¬ p3954) ∨ (¬ p4604) ∨ (¬ p5190))
    : p2829 ∨ (¬ p3917) ∨ (¬ p3389) ∨ p2608 ∨ (¬ p5190) ∨ (¬ p2459) ∨ (¬ p4604) ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42234 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step90492 (p2177 p2311 p2341 p2406 p2427 p2598 p2785 p2829 p3551 p3590 p3688 p4556 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73444 : p3688 ∨ p2829)
    (h71856 : (¬ p3688) ∨ (¬ p2406) ∨ (¬ p2785) ∨ (¬ p2598) ∨ (¬ p3590) ∨ (¬ p3551) ∨ (¬ p2427) ∨ (¬ p2311) ∨ (¬ p4556) ∨ (¬ p2177))
    : (¬ p2785) ∨ p2341 ∨ (¬ p2311) ∨ (¬ p2406) ∨ (¬ p2598) ∨ (¬ p3590) ∨ (¬ p2427) ∨ p2829 ∨ (¬ p4556) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2785 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h71856 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step90493 (p2177 p2311 p2341 p2396 p2785 p2829 p3551 p3688 p4107 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73444 : p3688 ∨ p2829)
    (h73514 : p4107 ∨ p2396)
    (h54910 : (¬ p2177) ∨ (¬ p2311) ∨ (¬ p2785) ∨ (¬ p3551) ∨ (¬ p3688) ∨ (¬ p4107))
    : p2341 ∨ p2829 ∨ (¬ p2311) ∨ (¬ p2785) ∨ (¬ p2177) ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h54910 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u8)))))))))))))

theorem step90497 (p2230 p2427 p2608 p2819 p2829 p2881 p3688 p3954 p4358 p4503 p5190 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h73498 : p3954 ∨ p2608)
    (h73444 : p3688 ∨ p2829)
    (h55910 : (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4358) ∨ (¬ p4503) ∨ (¬ p5190))
    : (¬ p2427) ∨ (¬ p2230) ∨ p2819 ∨ p2608 ∨ (¬ p2881) ∨ (¬ p5190) ∨ (¬ p4503) ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h55910 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step90502 (p2248 p2449 p2608 p2761 p2807 p2829 p3688 p3954 p4329 p5254 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73444 : p3688 ∨ p2829)
    (h48847 : (¬ p2248) ∨ (¬ p2449) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4329) ∨ (¬ p5254))
    : (¬ p4329) ∨ (¬ p2449) ∨ (¬ p2248) ∨ (¬ p2761) ∨ p2608 ∨ (¬ p5254) ∨ p2829 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4329 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h48847 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step90503 (p2122 p2248 p2449 p2608 p2807 p2829 p3246 p3688 p3690 p3822 p3954 p4556 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73446 : p3690 ∨ p3246)
    (h73444 : p3688 ∨ p2829)
    (h73472 : p3822 ∨ p2122)
    (h57790 : (¬ p2248) ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p3688) ∨ (¬ p3690) ∨ (¬ p3822) ∨ (¬ p3954) ∨ (¬ p4556))
    : (¬ p2449) ∨ p2608 ∨ (¬ p4556) ∨ (¬ p2248) ∨ (¬ p2807) ∨ p3246 ∨ p2829 ∨ p2122 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h57790 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step90505 (p2122 p2248 p2264 p2608 p2807 p2829 p2881 p3570 p3688 p3822 p3954 p4556 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73444 : p3688 ∨ p2829)
    (h73472 : p3822 ∨ p2122)
    (h73498 : p3954 ∨ p2608)
    (h63777 : (¬ p2248) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p3570) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p3954) ∨ (¬ p4556))
    : (¬ p2264) ∨ p2881 ∨ p2829 ∨ p2122 ∨ (¬ p2807) ∨ (¬ p2248) ∨ p2608 ∨ (¬ p4556) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h63777 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step90506 (p2177 p2299 p2307 p2313 p2696 p2742 p2785 p2829 p2992 p3156 p3688 p4902 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73238 : p2313 ∨ p2307)
    (h73234 : p2299 ∨ p2177)
    (h71857 : (¬ p2742) ∨ (¬ p3688) ∨ (¬ p2696) ∨ (¬ p2785) ∨ (¬ p2992) ∨ (¬ p3156) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p4902))
    : (¬ p2992) ∨ p2829 ∨ (¬ p4902) ∨ (¬ p2742) ∨ p2307 ∨ (¬ p3156) ∨ p2177 ∨ (¬ p2696) ∨ (¬ p2785) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h71857 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step90511 (p2363 p2737 p2829 p3609 p3688 p4078 p4340 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h73444 : p3688 ∨ p2829)
    (h61940 : (¬ p2363) ∨ (¬ p2737) ∨ (¬ p3688) ∨ (¬ p4078) ∨ (¬ p4340))
    : p3609 ∨ p2829 ∨ (¬ p2737) ∨ (¬ p2363) ∨ (¬ p4078) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4078 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h61940 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step90512 (p2264 p2363 p2598 p2829 p3201 p3609 p3688 p3740 p4078 p4340 p4503 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73558 : p4340 ∨ p3609)
    (h71859 : (¬ p4340) ∨ (¬ p3201) ∨ (¬ p4078) ∨ (¬ p4503) ∨ (¬ p3688) ∨ (¬ p2264) ∨ (¬ p3740) ∨ (¬ p2598) ∨ (¬ p2363))
    : p2829 ∨ (¬ p4503) ∨ (¬ p4078) ∨ p3609 ∨ (¬ p2363) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3740) ∨ (¬ p2264) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4078 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71859 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step90513 (p2254 p2264 p2707 p2774 p2807 p2829 p2881 p3414 p3553 p3589 p3688 p4895 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73392 : p3414 ∨ p2807)
    (h73410 : p3553 ∨ p2264)
    (h57326 : (¬ p2254) ∨ (¬ p2707) ∨ (¬ p2774) ∨ (¬ p2881) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3589) ∨ (¬ p3688) ∨ (¬ p4895))
    : p2829 ∨ (¬ p2707) ∨ (¬ p3589) ∨ (¬ p2774) ∨ p2807 ∨ (¬ p4895) ∨ p2264 ∨ (¬ p2254) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4895 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h57326 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step90518 (p2363 p2608 p2819 p2829 p3688 p3954 p4347 p4358 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73564 : p4358 ∨ p2819)
    (h73444 : p3688 ∨ p2829)
    (h73498 : p3954 ∨ p2608)
    (h45745 : (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4347) ∨ (¬ p4358))
    : p2363 ∨ p2819 ∨ p2829 ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45745 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step90520 (p2187 p2737 p2819 p2829 p3688 p4358 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73564 : p4358 ∨ p2819)
    (h46806 : (¬ p2187) ∨ (¬ p2737) ∨ (¬ p3688) ∨ (¬ p4358))
    : (¬ p2737) ∨ (¬ p2187) ∨ p2829 ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46806 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step90521 (p2785 p2829 p3125 p3367 p3654 p3688 p3946 : Prop)
    (h73492 : p3946 ∨ p3654)
    (h73444 : p3688 ∨ p2829)
    (h62153 : (¬ p2785) ∨ (¬ p3125) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p3946))
    : p3654 ∨ (¬ p3125) ∨ (¬ p3367) ∨ (¬ p2785) ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3654) := (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62153 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step90522 (p2274 p2295 p2737 p2829 p3568 p3688 p4337 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73444 : p3688 ∨ p2829)
    (h45314 : (¬ p2274) ∨ (¬ p2737) ∨ (¬ p3568) ∨ (¬ p3688) ∨ (¬ p4337))
    : (¬ p4337) ∨ p2295 ∨ p2829 ∨ (¬ p2737) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4337 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45314 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step90523 (p2248 p2608 p2829 p2901 p2946 p3246 p3688 p3917 p3954 p4625 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73498 : p3954 ∨ p2608)
    (h48891 : (¬ p2248) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3688) ∨ (¬ p3917) ∨ (¬ p3954) ∨ (¬ p4625))
    : p2829 ∨ (¬ p3246) ∨ (¬ p2901) ∨ (¬ p4625) ∨ (¬ p3917) ∨ (¬ p2248) ∨ (¬ p2946) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h48891 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step90524 (p2352 p2608 p2819 p2829 p3688 p3954 p4358 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h73444 : p3688 ∨ p2829)
    (h73498 : p3954 ∨ p2608)
    (h48680 : (¬ p2352) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4358))
    : (¬ p2352) ∨ p2819 ∨ p2829 ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48680 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90525 (p2352 p2819 p2829 p3367 p3688 p4358 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73564 : p4358 ∨ p2819)
    (h43129 : (¬ p2352) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p4358))
    : (¬ p3367) ∨ p2829 ∨ (¬ p2352) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43129 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step90526 (p2668 p2737 p2819 p2829 p3688 p4358 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73564 : p4358 ∨ p2819)
    (h46604 : (¬ p2668) ∨ (¬ p2737) ∨ (¬ p3688) ∨ (¬ p4358))
    : (¬ p2668) ∨ p2829 ∨ p2819 ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46604 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step90527 (p2383 p2737 p2819 p2829 p3688 p4358 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h73444 : p3688 ∨ p2829)
    (h54551 : (¬ p2383) ∨ (¬ p2737) ∨ (¬ p3688) ∨ (¬ p4358))
    : (¬ p2383) ∨ p2819 ∨ (¬ p2737) ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54551 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90528 (p2295 p2696 p2737 p2829 p3365 p3568 p3688 p3873 p4337 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h73444 : p3688 ∨ p2829)
    (h73416 : p3568 ∨ p2295)
    (h46353 : (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3568) ∨ (¬ p3688) ∨ (¬ p3873) ∨ (¬ p4337))
    : (¬ p4337) ∨ p2696 ∨ (¬ p2737) ∨ (¬ p3873) ∨ p2829 ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4337 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u8 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h46353 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step90529 (p2696 p2774 p2829 p3365 p3367 p3688 p4752 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73390 : p3365 ∨ p2696)
    (h41411 : (¬ p2774) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p4752))
    : p2829 ∨ (¬ p2774) ∨ p2696 ∨ (¬ p4752) ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41411 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step90530 (p2696 p2774 p2829 p3365 p3367 p3688 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73390 : p3365 ∨ p2696)
    (h58527 : (¬ p2774) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3688))
    : p2829 ∨ (¬ p2774) ∨ (¬ p3367) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h58527 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90533 (p2819 p2829 p3266 p3322 p3461 p3688 p4191 p4358 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73564 : p4358 ∨ p2819)
    (h73444 : p3688 ∨ p2829)
    (h42938 : (¬ p3266) ∨ (¬ p3322) ∨ (¬ p3688) ∨ (¬ p4191) ∨ (¬ p4358))
    : p3461 ∨ (¬ p3266) ∨ p2819 ∨ p2829 ∨ (¬ p3322) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42938 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step90534 (p2608 p2829 p3461 p3688 p3917 p3954 p4191 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73498 : p3954 ∨ p2608)
    (h73530 : p4191 ∨ p3461)
    (h57451 : (¬ p3688) ∨ (¬ p3917) ∨ (¬ p3954) ∨ (¬ p4191))
    : p2829 ∨ p2608 ∨ p3461 ∨ (¬ p3917) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h57451 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step90537 (p2241 p2247 p2744 p2829 p3449 p3461 p3688 p3917 p4181 p4191 p5119 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73530 : p4191 ∨ p3461)
    (h73226 : p2247 ∨ p2241)
    (h52553 : (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3449) ∨ (¬ p3688) ∨ (¬ p3917) ∨ (¬ p4181) ∨ (¬ p4191) ∨ (¬ p5119))
    : (¬ p4181) ∨ p2829 ∨ (¬ p5119) ∨ p3461 ∨ (¬ p2744) ∨ (¬ p3449) ∨ p2241 ∨ (¬ p3917) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4181 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h52553 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step90538 (p2248 p2459 p2608 p2807 p2819 p2829 p3256 p3688 p3954 p4044 p4348 p4358 p4503 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73564 : p4358 ∨ p2819)
    (h73562 : p4348 ∨ p2459)
    (h73498 : p3954 ∨ p2608)
    (h55626 : (¬ p2248) ∨ (¬ p2807) ∨ (¬ p3256) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4044) ∨ (¬ p4348) ∨ (¬ p4358) ∨ (¬ p4503))
    : p2829 ∨ (¬ p2248) ∨ p2819 ∨ p2459 ∨ (¬ p4503) ∨ p2608 ∨ (¬ p4044) ∨ (¬ p2807) ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h55626 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step90542 (p2241 p2247 p2363 p2744 p2819 p2829 p3449 p3688 p4009 p4288 p4347 p4358 p5122 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73226 : p2247 ∨ p2241)
    (h73564 : p4358 ∨ p2819)
    (h73444 : p3688 ∨ p2829)
    (h52555 : (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3449) ∨ (¬ p3688) ∨ (¬ p4009) ∨ (¬ p4288) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p5122))
    : (¬ p4009) ∨ p2363 ∨ p2241 ∨ p2819 ∨ (¬ p4288) ∨ p2829 ∨ (¬ p3449) ∨ (¬ p5122) ∨ (¬ p2744) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4009 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4288 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h52555 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step90544 (p2753 p2774 p2829 p3688 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h5869 : (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3688))
    : p2829 ∨ (¬ p2753) ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h5869 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step90545 (p2098 p2122 p2753 p2829 p3688 p3822 p4326 p4405 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73472 : p3822 ∨ p2122)
    (h41859 : (¬ p2098) ∨ (¬ p2753) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p4326) ∨ (¬ p4405))
    : p2829 ∨ (¬ p4326) ∨ (¬ p2098) ∨ (¬ p4405) ∨ p2122 ∨ (¬ p2753) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p4326 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41859 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step90548 (p2608 p2829 p3379 p3688 p3954 p4030 p5221 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73444 : p3688 ∨ p2829)
    (h48001 : (¬ p3379) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4030) ∨ (¬ p5221))
    : p2608 ∨ p2829 ∨ (¬ p4030) ∨ (¬ p5221) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5221 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h48001 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step90550 (p2122 p2598 p2829 p3055 p3367 p3688 p3822 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73472 : p3822 ∨ p2122)
    (h73350 : p3055 ∨ p2598)
    (h57432 : (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p3822))
    : p2829 ∨ (¬ p3367) ∨ p2122 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h57432 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step90551 (p2177 p2299 p2307 p2313 p2785 p2829 p3367 p3688 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73238 : p2313 ∨ p2307)
    (h73234 : p2299 ∨ p2177)
    (h45360 : (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2785) ∨ (¬ p3367) ∨ (¬ p3688))
    : p2829 ∨ p2307 ∨ (¬ p2785) ∨ (¬ p3367) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45360 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step90552 (p2311 p2396 p2785 p2829 p3367 p3516 p3688 p3821 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73444 : p3688 ∨ p2829)
    (h48813 : (¬ p2311) ∨ (¬ p2396) ∨ (¬ p2785) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p3821))
    : p3516 ∨ (¬ p2311) ∨ (¬ p2785) ∨ (¬ p3367) ∨ (¬ p2396) ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h48813 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step90555 (p2352 p2363 p2578 p2785 p2829 p3367 p3688 p3956 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73500 : p3956 ∨ p2352)
    (h73444 : p3688 ∨ p2829)
    (h45358 : (¬ p2578) ∨ (¬ p2785) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p3956) ∨ (¬ p4347))
    : p2363 ∨ (¬ p2578) ∨ (¬ p3367) ∨ p2352 ∨ p2829 ∨ (¬ p2785) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45358 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step90558 (p2774 p2829 p3367 p3425 p3688 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h52413 : (¬ p2774) ∨ (¬ p3367) ∨ (¬ p3425) ∨ (¬ p3688))
    : (¬ p3425) ∨ p2829 ∨ (¬ p3367) ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3425 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h52413 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90559 (p2307 p2313 p2553 p2785 p2829 p3367 p3688 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73238 : p2313 ∨ p2307)
    (h43976 : (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2785) ∨ (¬ p3367) ∨ (¬ p3688))
    : p2829 ∨ p2307 ∨ (¬ p2785) ∨ (¬ p3367) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43976 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step90562 (p2248 p2528 p2608 p2651 p2829 p3083 p3688 p3917 p3954 p4604 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73498 : p3954 ∨ p2608)
    (h61615 : (¬ p2248) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p3688) ∨ (¬ p3917) ∨ (¬ p3954) ∨ (¬ p4604))
    : (¬ p3083) ∨ p2829 ∨ (¬ p4604) ∨ (¬ p3917) ∨ p2608 ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p2248) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3083 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h61615 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step90568 (p2707 p2819 p2829 p3425 p3688 p3873 p4358 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73564 : p4358 ∨ p2819)
    (h63653 : (¬ p2707) ∨ (¬ p3425) ∨ (¬ p3688) ∨ (¬ p3873) ∨ (¬ p4358))
    : (¬ p2707) ∨ p2829 ∨ p2819 ∨ (¬ p3873) ∨ (¬ p3425) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h63653 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step90570 (p2220 p2459 p2608 p2819 p2829 p3146 p3688 p3954 p4348 p4358 p4503 p4521 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h73444 : p3688 ∨ p2829)
    (h73562 : p4348 ∨ p2459)
    (h73498 : p3954 ∨ p2608)
    (h54462 : (¬ p2220) ∨ (¬ p3146) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4348) ∨ (¬ p4358) ∨ (¬ p4503) ∨ (¬ p4521))
    : (¬ p4503) ∨ (¬ p3146) ∨ p2819 ∨ p2829 ∨ p2459 ∨ (¬ p4521) ∨ (¬ p2220) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4503 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h54462 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step90572 (p2122 p2187 p2248 p2284 p2608 p2829 p2946 p3688 p3822 p3954 p4405 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73444 : p3688 ∨ p2829)
    (h73498 : p3954 ∨ p2608)
    (h49142 : (¬ p2187) ∨ (¬ p2248) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p3954) ∨ (¬ p4405))
    : p2122 ∨ (¬ p2248) ∨ (¬ p2187) ∨ (¬ p4405) ∨ p2829 ∨ (¬ p2284) ∨ (¬ p2946) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h49142 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step90577 (p2608 p2819 p2829 p3688 p3954 p4113 p4114 p4358 p5017 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73444 : p3688 ∨ p2829)
    (h73564 : p4358 ∨ p2819)
    (h46734 : (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4113) ∨ (¬ p4114) ∨ (¬ p4358) ∨ (¬ p5017))
    : (¬ p4114) ∨ (¬ p5017) ∨ p2608 ∨ p2829 ∨ (¬ p4113) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4114 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5017 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4113 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h46734 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step90578 (p2352 p2383 p2387 p2553 p2588 p2785 p2829 p3688 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h73444 : p3688 ∨ p2829)
    (h73282 : p2588 ∨ p2553)
    (h43016 : (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2588) ∨ (¬ p2785) ∨ (¬ p3688))
    : (¬ p2785) ∨ (¬ p2352) ∨ p2383 ∨ p2829 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2785 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43016 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step90582 (p2132 p2138 p2383 p2786 p2819 p2829 p3688 p4358 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h73214 : p2138 ∨ p2132)
    (h73444 : p3688 ∨ p2829)
    (h43470 : (¬ p2138) ∨ (¬ p2383) ∨ (¬ p2786) ∨ (¬ p3688) ∨ (¬ p4358))
    : (¬ p2383) ∨ p2819 ∨ (¬ p2786) ∨ p2132 ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43470 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step90583 (p2144 p2383 p2819 p2829 p2962 p3688 p4358 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h73444 : p3688 ∨ p2829)
    (h71862 : (¬ p4358) ∨ (¬ p3688) ∨ (¬ p2962) ∨ (¬ p2144) ∨ (¬ p2383))
    : (¬ p2383) ∨ p2819 ∨ (¬ p2962) ∨ (¬ p2144) ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h71862 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step90585 (p2553 p2588 p2707 p2829 p3688 p4475 p5225 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73282 : p2588 ∨ p2553)
    (h48335 : (¬ p2588) ∨ (¬ p2707) ∨ (¬ p3688) ∨ (¬ p4475) ∨ (¬ p5225))
    : p2829 ∨ (¬ p2707) ∨ p2553 ∨ (¬ p5225) ∨ (¬ p4475) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5225 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48335 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step90586 (p2274 p2707 p2829 p3097 p3688 p4401 p4475 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73352 : p3097 ∨ p2274)
    (h53794 : (¬ p2707) ∨ (¬ p3097) ∨ (¬ p3688) ∨ (¬ p4401) ∨ (¬ p4475))
    : (¬ p4475) ∨ p2829 ∨ (¬ p2707) ∨ (¬ p4401) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4475 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4401 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h53794 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step90587 (p2122 p2307 p2829 p3688 p3822 p3987 p4117 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73444 : p3688 ∨ p2829)
    (h71863 : (¬ p3822) ∨ (¬ p3688) ∨ (¬ p3987) ∨ (¬ p4117) ∨ (¬ p2307))
    : p2122 ∨ p2829 ∨ (¬ p4117) ∨ (¬ p3987) ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71863 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step90589 (p2122 p2608 p2829 p3309 p3688 p3822 p3954 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73472 : p3822 ∨ p2122)
    (h73498 : p3954 ∨ p2608)
    (h47436 : (¬ p3309) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p3954))
    : p2829 ∨ p2122 ∨ p2608 ∨ (¬ p3309) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47436 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step90590 (p2122 p2553 p2608 p2829 p3660 p3688 p3822 p3954 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73498 : p3954 ∨ p2608)
    (h73472 : p3822 ∨ p2122)
    (h57259 : (¬ p2553) ∨ (¬ p3660) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p3954))
    : p2829 ∨ p2608 ∨ (¬ p2553) ∨ p2122 ∨ (¬ p3660) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h57259 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step90592 (p2156 p2427 p2860 p3051 p3646 p4235 p4885 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73436 : p3646 ∨ p2156)
    (h49013 : (¬ p2860) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4235) ∨ (¬ p4885))
    : (¬ p3051) ∨ (¬ p2860) ∨ p2427 ∨ (¬ p4885) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49013 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step90593 (p2274 p2553 p2588 p2590 p2860 p4885 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h41068 : (¬ p2274) ∨ (¬ p2588) ∨ (¬ p2590) ∨ (¬ p2860) ∨ (¬ p4885))
    : (¬ p2860) ∨ (¬ p2590) ∨ (¬ p2274) ∨ (¬ p4885) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2860 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41068 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step90597 (p2386 p2440 p2542 p2860 p3016 p3574 p3743 p4885 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73270 : p2542 ∨ p2440)
    (h42203 : (¬ p2386) ∨ (¬ p2542) ∨ (¬ p2860) ∨ (¬ p3574) ∨ (¬ p3743) ∨ (¬ p4885))
    : p3016 ∨ p2440 ∨ (¬ p3743) ∨ (¬ p2386) ∨ (¬ p4885) ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3016) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42203 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step90598 (p2220 p2427 p2619 p3051 p4120 p4235 p4885 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h73536 : p4235 ∨ p2427)
    (h54726 : (¬ p2619) ∨ (¬ p3051) ∨ (¬ p4120) ∨ (¬ p4235) ∨ (¬ p4885))
    : (¬ p3051) ∨ (¬ p2619) ∨ (¬ p4885) ∨ p2220 ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54726 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step90601 (p2437 p2440 p2542 p2870 p3742 p4001 p4885 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73270 : p2542 ∨ p2440)
    (h51317 : (¬ p2542) ∨ (¬ p2870) ∨ (¬ p3742) ∨ (¬ p4001) ∨ (¬ p4885))
    : (¬ p2870) ∨ p2437 ∨ (¬ p4885) ∨ (¬ p4001) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51317 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step90603 (p2440 p2542 p2619 p3083 p4885 p5007 : Prop)
    (h73872 : p5007 ∨ p3083)
    (h73270 : p2542 ∨ p2440)
    (h65955 : (¬ p5007) ∨ (¬ p2542) ∨ (¬ p4885) ∨ (¬ p2619))
    : (¬ p2619) ∨ p3083 ∨ p2440 ∨ (¬ p4885) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p5007 := (Or.elim h73872 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h65955 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step90607 (p3367 p3590 p6046 : Prop)
    (h74385 : p3367 ∨ (¬ p6046))
    (h13275 : p3590 ∨ p6046)
    : p3590 ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3590) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3367) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6046) := (Or.elim h74385 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13275 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step90608 (p3367 p4257 p6046 : Prop)
    (h74385 : p3367 ∨ (¬ p6046))
    (h13276 : p4257 ∨ p6046)
    : p4257 ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4257) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3367) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6046) := (Or.elim h74385 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13276 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step90612 (p2132 p2427 p2563 p2860 p4110 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h55352 : (¬ p2132) ∨ (¬ p2427) ∨ (¬ p2860) ∨ (¬ p4110))
    : (¬ p2427) ∨ (¬ p2860) ∨ (¬ p2132) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55352 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90615 (p2132 p2563 p2598 p2860 p3055 p4110 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h73350 : p3055 ∨ p2598)
    (h47352 : (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3055) ∨ (¬ p4110))
    : (¬ p2132) ∨ (¬ p2860) ∨ p2563 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47352 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90617 (p2132 p2373 p2427 p2870 p4235 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h46493 : (¬ p2132) ∨ (¬ p2373) ∨ (¬ p2870) ∨ (¬ p4235))
    : (¬ p2870) ∨ (¬ p2132) ∨ p2427 ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46493 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90619 (p2132 p2284 p2860 p2901 p3952 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h43062 : (¬ p2132) ∨ (¬ p2860) ∨ (¬ p2901) ∨ (¬ p3952))
    : (¬ p2901) ∨ p2284 ∨ (¬ p2132) ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43062 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90623 (p2132 p2573 p2579 p2753 p2870 p3347 p3461 p3564 p4129 p4137 p4191 p4826 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h73530 : p4191 ∨ p3461)
    (h73274 : p2579 ∨ p2573)
    (h71867 : (¬ p4129) ∨ (¬ p4137) ∨ (¬ p2132) ∨ (¬ p4191) ∨ (¬ p3347) ∨ (¬ p2579) ∨ (¬ p4826) ∨ (¬ p2870) ∨ (¬ p2753))
    : (¬ p4129) ∨ (¬ p2753) ∨ p3564 ∨ p3461 ∨ (¬ p3347) ∨ (¬ p2132) ∨ (¬ p4826) ∨ p2573 ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4129 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h71867 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step90624 (p2132 p2192 p2860 p4173 p4874 : Prop)
    (h73528 : p4173 ∨ p2192)
    (h71868 : (¬ p4874) ∨ (¬ p4173) ∨ (¬ p2132) ∨ (¬ p2860))
    : (¬ p2860) ∨ (¬ p2132) ∨ (¬ p4874) ∨ p2192 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2860 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71868 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step90625 (p2132 p2870 p2891 p3486 p4874 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h71869 : (¬ p4874) ∨ (¬ p3486) ∨ (¬ p2132) ∨ (¬ p2870))
    : (¬ p2870) ∨ (¬ p2132) ∨ (¬ p4874) ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71869 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step90626 (p2132 p2839 p3399 p3583 p3589 p4366 p4793 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73424 : p3583 ∨ p2839)
    (h41213 : (¬ p2132) ∨ (¬ p3583) ∨ (¬ p3589) ∨ (¬ p4366) ∨ (¬ p4793))
    : (¬ p4793) ∨ p3399 ∨ (¬ p2132) ∨ (¬ p3589) ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4793 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41213 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step90627 (p2132 p2641 p2749 p2797 p2839 p3583 p4195 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73424 : p3583 ∨ p2839)
    (h45227 : (¬ p2132) ∨ (¬ p2641) ∨ (¬ p2749) ∨ (¬ p3583) ∨ (¬ p4195))
    : (¬ p2641) ∨ p2797 ∨ (¬ p2749) ∨ (¬ p2132) ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45227 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step90632 (p2132 p2737 p2743 p2891 p3166 p3172 p3246 p3256 p3361 p3950 p4118 p4418 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h73298 : p2743 ∨ p2737)
    (h73520 : p4118 ∨ p3256)
    (h71871 : (¬ p3172) ∨ (¬ p2743) ∨ (¬ p3361) ∨ (¬ p3246) ∨ (¬ p4418) ∨ (¬ p2132) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p2891))
    : p3166 ∨ p2737 ∨ (¬ p3361) ∨ (¬ p2132) ∨ (¬ p2891) ∨ (¬ p4418) ∨ p3256 ∨ (¬ p3246) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h71871 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step90633 (p2132 p2440 p2542 p2839 p2850 p3016 p3201 p3362 p3363 p3574 p3583 p3684 p3698 p3876 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73422 : p3574 ∨ p3016)
    (h73442 : p3684 ∨ p2850)
    (h73424 : p3583 ∨ p2839)
    (h73486 : p3876 ∨ p3201)
    (h66701 : (¬ p3583) ∨ (¬ p3876) ∨ (¬ p3574) ∨ (¬ p3684) ∨ (¬ p3698) ∨ (¬ p3362) ∨ (¬ p3363) ∨ (¬ p2132) ∨ (¬ p2542))
    : p2440 ∨ p3016 ∨ p2850 ∨ (¬ p3698) ∨ (¬ p2132) ∨ (¬ p3363) ∨ p2839 ∨ p3201 ∨ (¬ p3362) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h66701 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step90634 (p2132 p2839 p3379 p3452 p3583 p3589 p4376 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73394 : p3452 ∨ p3379)
    (h49038 : (¬ p2132) ∨ (¬ p3452) ∨ (¬ p3583) ∨ (¬ p3589) ∨ (¬ p4376))
    : p2839 ∨ p3379 ∨ (¬ p4376) ∨ (¬ p3589) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2839) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h49038 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step90635 (p2132 p2619 p2774 p2780 p3745 p4337 p4509 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h53804 : (¬ p2132) ∨ (¬ p2619) ∨ (¬ p2780) ∨ (¬ p3745) ∨ (¬ p4337) ∨ (¬ p4509))
    : (¬ p4337) ∨ (¬ p3745) ∨ (¬ p2132) ∨ (¬ p2619) ∨ p2774 ∨ (¬ p4509) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4337 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h53804 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step90637 (p2132 p2192 p2274 p2598 p3055 p4418 : Prop)
    (h73350 : p3055 ∨ p2598)
    (h58969 : (¬ p2132) ∨ (¬ p2192) ∨ (¬ p2274) ∨ (¬ p3055) ∨ (¬ p4418))
    : (¬ p2132) ∨ (¬ p2274) ∨ p2598 ∨ (¬ p4418) ∨ (¬ p2192) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h58969 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step90638 (p2132 p2192 p2274 p2331 p2737 p2743 p2963 p3323 p3361 p4037 p4418 p4620 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73338 : p2963 ∨ p2331)
    (h73508 : p4037 ∨ p3323)
    (h71872 : (¬ p4037) ∨ (¬ p4418) ∨ (¬ p3361) ∨ (¬ p2192) ∨ (¬ p2963) ∨ (¬ p2274) ∨ (¬ p4620) ∨ (¬ p2743) ∨ (¬ p2132))
    : (¬ p2274) ∨ (¬ p4620) ∨ (¬ p2132) ∨ p2737 ∨ (¬ p4418) ∨ p2331 ∨ p3323 ∨ (¬ p3361) ∨ (¬ p2192) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h71872 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step90639 (p2132 p2192 p2274 p2331 p2668 p2737 p2743 p2963 p3324 p3361 p4418 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73338 : p2963 ∨ p2331)
    (h73386 : p3324 ∨ p2668)
    (h71873 : (¬ p2192) ∨ (¬ p2743) ∨ (¬ p3324) ∨ (¬ p2963) ∨ (¬ p3361) ∨ (¬ p2132) ∨ (¬ p4418) ∨ (¬ p2274))
    : p2737 ∨ (¬ p2274) ∨ (¬ p2192) ∨ (¬ p3361) ∨ (¬ p2132) ∨ p2331 ∨ (¬ p4418) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h71873 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step90642 (p2132 p2427 p2563 p2870 p4235 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h52015 : (¬ p2132) ∨ (¬ p2563) ∨ (¬ p2870) ∨ (¬ p4235))
    : (¬ p2870) ∨ p2427 ∨ (¬ p2132) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h52015 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90645 (p2132 p2284 p3105 p3115 p4208 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h45704 : (¬ p2132) ∨ (¬ p2284) ∨ (¬ p3105) ∨ (¬ p4208))
    : (¬ p3105) ∨ p3115 ∨ (¬ p2284) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45704 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90648 (p2132 p2177 p2254 p2264 p2707 p2807 p2839 p3414 p3553 p3583 p3589 p4473 : Prop)
    (h73392 : p3414 ∨ p2807)
    (h73410 : p3553 ∨ p2264)
    (h73424 : p3583 ∨ p2839)
    (h57598 : (¬ p2132) ∨ (¬ p2177) ∨ (¬ p2254) ∨ (¬ p2707) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3583) ∨ (¬ p3589) ∨ (¬ p4473))
    : (¬ p2707) ∨ (¬ p4473) ∨ (¬ p2177) ∨ (¬ p2254) ∨ p2807 ∨ (¬ p2132) ∨ p2264 ∨ (¬ p3589) ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4473 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h57598 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step90652 (p2132 p2254 p2264 p2459 p2563 p2807 p2982 p3105 p3414 p3553 p3589 p4348 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h73562 : p4348 ∨ p2459)
    (h73410 : p3553 ∨ p2264)
    (h73392 : p3414 ∨ p2807)
    (h58201 : (¬ p2132) ∨ (¬ p2254) ∨ (¬ p2563) ∨ (¬ p3105) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3589) ∨ (¬ p4348) ∨ (¬ p4948))
    : p2982 ∨ (¬ p2254) ∨ p2459 ∨ (¬ p3105) ∨ p2264 ∨ (¬ p3589) ∨ (¬ p2563) ∨ (¬ p2132) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h58201 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step90653 (p2132 p2341 p2417 p2860 p2911 p3125 p3551 p4278 p4621 p4729 p5197 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73408 : p3551 ∨ p2341)
    (h50772 : (¬ p2132) ∨ (¬ p2860) ∨ (¬ p2911) ∨ (¬ p3125) ∨ (¬ p3551) ∨ (¬ p4278) ∨ (¬ p4621) ∨ (¬ p4729) ∨ (¬ p5197))
    : (¬ p2911) ∨ (¬ p4621) ∨ (¬ p5197) ∨ (¬ p2860) ∨ (¬ p2132) ∨ (¬ p4729) ∨ p2417 ∨ p2341 ∨ (¬ p3125) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u10 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h50772 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step90655 (p2132 p2417 p2437 p2651 p2657 p2870 p2881 p3742 p4278 p4666 p4789 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73452 : p3742 ∨ p2437)
    (h73288 : p2657 ∨ p2651)
    (h41668 : (¬ p2132) ∨ (¬ p2657) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p4789))
    : p2417 ∨ (¬ p2870) ∨ p2437 ∨ p2651 ∨ (¬ p2881) ∨ (¬ p4789) ∨ (¬ p2132) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41668 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step90656 (p2132 p2417 p2437 p2619 p2651 p2657 p3146 p3742 p4278 p4669 p4789 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73288 : p2657 ∨ p2651)
    (h73452 : p3742 ∨ p2437)
    (h55441 : (¬ p2132) ∨ (¬ p2619) ∨ (¬ p2657) ∨ (¬ p3146) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4789))
    : (¬ p3146) ∨ p2417 ∨ (¬ p4789) ∨ (¬ p2619) ∨ (¬ p4669) ∨ p2651 ∨ p2437 ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h55441 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step90659 (p2132 p2187 p2753 p2860 p2911 p2927 p3379 p3399 p3644 p4133 p4366 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73570 : p4366 ∨ p3399)
    (h71875 : (¬ p2132) ∨ (¬ p3379) ∨ (¬ p2860) ∨ (¬ p3644) ∨ (¬ p4366) ∨ (¬ p2753) ∨ (¬ p4133) ∨ (¬ p2187) ∨ (¬ p2927))
    : (¬ p2132) ∨ p2911 ∨ (¬ p2927) ∨ p3399 ∨ (¬ p3379) ∨ (¬ p2753) ∨ (¬ p4133) ∨ (¬ p2187) ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2911) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2927 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71875 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step90660 (p2132 p2241 p2750 p2753 p2870 p3093 p3246 p3319 p3591 p4026 p4625 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73504 : p4026 ∨ p3319)
    (h55772 : (¬ p2132) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4625))
    : (¬ p2241) ∨ p3093 ∨ (¬ p3246) ∨ (¬ p2753) ∨ (¬ p4625) ∨ p3319 ∨ (¬ p2132) ∨ (¬ p2750) ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h55772 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step90663 (p2132 p2363 p2870 p3093 p3246 p3591 p3923 p3950 p4347 p4733 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73560 : p4347 ∨ p2363)
    (h50721 : (¬ p2132) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p3950) ∨ (¬ p4347) ∨ (¬ p4733))
    : (¬ p3246) ∨ p3093 ∨ (¬ p2132) ∨ p2363 ∨ (¬ p3950) ∨ (¬ p3923) ∨ (¬ p2870) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50721 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step90664 (p2132 p2528 p2534 p2651 p2657 p2870 p3083 p3246 p3950 p4256 p4789 : Prop)
    (h73542 : p4256 ∨ p3083)
    (h73268 : p2534 ∨ p2528)
    (h73288 : p2657 ∨ p2651)
    (h55339 : (¬ p2132) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p4256) ∨ (¬ p4789))
    : p3083 ∨ p2528 ∨ (¬ p2132) ∨ (¬ p2870) ∨ (¬ p4789) ∨ p2651 ∨ (¬ p3950) ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h55339 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step90665 (p2132 p2352 p2363 p2573 p2579 p2870 p3246 p3950 p3956 p4347 p4729 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73500 : p3956 ∨ p2352)
    (h73274 : p2579 ∨ p2573)
    (h62892 : (¬ p2132) ∨ (¬ p2579) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p4729))
    : (¬ p3246) ∨ p2363 ∨ p2352 ∨ (¬ p4729) ∨ (¬ p3950) ∨ (¬ p2132) ∨ p2573 ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h62892 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step90666 (p2132 p2528 p2870 p2881 p3166 p3172 p3256 p4118 p4438 p4789 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h73520 : p4118 ∨ p3256)
    (h42259 : (¬ p2132) ∨ (¬ p2528) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4438) ∨ (¬ p4789))
    : p3166 ∨ p3256 ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p4789) ∨ (¬ p2132) ∨ (¬ p2528) ∨ (¬ p4438) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42259 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step90669 (p2132 p2252 p2528 p2534 p2651 p2657 p2750 p2753 p2870 p3083 p3246 p3950 p4256 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73542 : p4256 ∨ p3083)
    (h73288 : p2657 ∨ p2651)
    (h64513 : (¬ p2132) ∨ (¬ p2252) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p4256))
    : (¬ p3950) ∨ p2528 ∨ (¬ p2252) ∨ (¬ p2870) ∨ (¬ p2753) ∨ (¬ p3246) ∨ p3083 ∨ (¬ p2132) ∨ p2651 ∨ (¬ p2750) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3950 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h64513 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (False.elim (r8 u11)))))))))))))))))))))

theorem step90670 (p2132 p2245 p2331 p2363 p2668 p2870 p2963 p3246 p3324 p3950 p4347 p4733 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73338 : p2963 ∨ p2331)
    (h73386 : p3324 ∨ p2668)
    (h56657 : (¬ p2132) ∨ (¬ p2245) ∨ (¬ p2870) ∨ (¬ p2963) ∨ (¬ p3246) ∨ (¬ p3324) ∨ (¬ p3950) ∨ (¬ p4347) ∨ (¬ p4733))
    : (¬ p3246) ∨ p2363 ∨ (¬ p2132) ∨ (¬ p2870) ∨ (¬ p3950) ∨ p2331 ∨ p2668 ∨ (¬ p2245) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h56657 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step90671 (p2132 p2363 p2619 p2753 p3093 p3449 p3860 p3969 p4347 p4870 p4993 p5122 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73482 : p3860 ∨ p3449)
    (h62894 : (¬ p2132) ∨ (¬ p2619) ∨ (¬ p2753) ∨ (¬ p3093) ∨ (¬ p3860) ∨ (¬ p3969) ∨ (¬ p4347) ∨ (¬ p4870) ∨ (¬ p4993) ∨ (¬ p5122))
    : (¬ p3969) ∨ p2363 ∨ p3449 ∨ (¬ p4993) ∨ (¬ p2753) ∨ (¬ p4870) ∨ (¬ p2619) ∨ (¬ p3093) ∨ (¬ p5122) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4993 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h62894 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step90673 (p2132 p2177 p2299 p2881 p2891 p4418 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h45713 : (¬ p2132) ∨ (¬ p2299) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p4418))
    : (¬ p2132) ∨ (¬ p4418) ∨ (¬ p2891) ∨ (¬ p2881) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45713 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step90674 (p2132 p2459 p2619 p3146 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h44673 : (¬ p2132) ∨ (¬ p2619) ∨ (¬ p3146) ∨ (¬ p4348))
    : (¬ p2619) ∨ (¬ p3146) ∨ p2459 ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44673 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90681 (p2132 p2493 p2499 p2598 p3055 p3695 p4030 p4715 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73350 : p3055 ∨ p2598)
    (h51486 : (¬ p2132) ∨ (¬ p2499) ∨ (¬ p3055) ∨ (¬ p3695) ∨ (¬ p4030) ∨ (¬ p4715))
    : (¬ p4030) ∨ (¬ p3695) ∨ (¬ p4715) ∨ (¬ p2132) ∨ p2493 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4030 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u7 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h51486 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step90682 (p2132 p2254 p2553 p2588 p2651 p2657 p2707 p2839 p3016 p3574 p3583 p3589 p4473 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73288 : p2657 ∨ p2651)
    (h73422 : p3574 ∨ p3016)
    (h73282 : p2588 ∨ p2553)
    (h56111 : (¬ p2132) ∨ (¬ p2254) ∨ (¬ p2588) ∨ (¬ p2657) ∨ (¬ p2707) ∨ (¬ p3574) ∨ (¬ p3583) ∨ (¬ p3589) ∨ (¬ p4473))
    : (¬ p2707) ∨ p2839 ∨ (¬ p4473) ∨ (¬ p2254) ∨ p2651 ∨ (¬ p2132) ∨ p3016 ∨ p2553 ∨ (¬ p3589) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4473 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h56111 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step90683 (p2132 p2352 p2753 p2870 p3246 p3564 p3923 p4137 p4625 p4870 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h49148 : (¬ p2132) ∨ (¬ p2352) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3923) ∨ (¬ p4137) ∨ (¬ p4625) ∨ (¬ p4870))
    : (¬ p2870) ∨ (¬ p2352) ∨ (¬ p4625) ∨ (¬ p2753) ∨ p3564 ∨ (¬ p3246) ∨ (¬ p2132) ∨ (¬ p3923) ∨ (¬ p4870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49148 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step90688 (p2132 p2352 p2573 p2579 p2753 p3105 p3347 p3680 p3956 p5123 p5580 : Prop)
    (h73500 : p3956 ∨ p2352)
    (h73274 : p2579 ∨ p2573)
    (h71880 : (¬ p5580) ∨ (¬ p3680) ∨ (¬ p2132) ∨ (¬ p2753) ∨ (¬ p5123) ∨ (¬ p3956) ∨ (¬ p3105) ∨ (¬ p2579) ∨ (¬ p3347))
    : (¬ p5580) ∨ (¬ p5123) ∨ (¬ p2132) ∨ (¬ p3347) ∨ (¬ p3680) ∨ (¬ p3105) ∨ p2352 ∨ p2573 ∨ (¬ p2753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u10 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h71880 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step90689 (p2132 p2396 p2870 p3246 p4107 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h46802 : (¬ p2132) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p4107))
    : (¬ p3246) ∨ p2396 ∨ (¬ p2870) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46802 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90691 (p2132 p3105 p3399 p3527 p3548 p3680 p4366 p4733 p5123 p5558 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73404 : p3548 ∨ p3527)
    (h62679 : (¬ p2132) ∨ (¬ p3105) ∨ (¬ p3548) ∨ (¬ p3680) ∨ (¬ p4366) ∨ (¬ p4733) ∨ (¬ p5123) ∨ (¬ p5558))
    : (¬ p5558) ∨ p3399 ∨ p3527 ∨ (¬ p4733) ∨ (¬ p5123) ∨ (¬ p3680) ∨ (¬ p2132) ∨ (¬ p3105) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5558 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h62679 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step90692 (p2132 p2187 p2459 p2528 p2534 p2860 p3389 p3540 p4133 p4186 p4729 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73402 : p3540 ∨ p3389)
    (h58086 : (¬ p2132) ∨ (¬ p2187) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (¬ p2860) ∨ (¬ p3540) ∨ (¬ p4133) ∨ (¬ p4186) ∨ (¬ p4729))
    : (¬ p2459) ∨ (¬ p4186) ∨ (¬ p2860) ∨ (¬ p4729) ∨ p2528 ∨ (¬ p2132) ∨ (¬ p2187) ∨ (¬ p4133) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4186 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h58086 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step90694 (p2132 p2274 p2774 p2780 p2839 p3097 p3583 p4428 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73352 : p3097 ∨ p2274)
    (h73424 : p3583 ∨ p2839)
    (h50293 : (¬ p2132) ∨ (¬ p2780) ∨ (¬ p3097) ∨ (¬ p3583) ∨ (¬ p4428))
    : p2774 ∨ (¬ p2132) ∨ p2274 ∨ p2839 ∨ (¬ p4428) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4428 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50293 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step90695 (p2132 p2187 p2774 p2780 p2839 p3583 p3989 p4428 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73424 : p3583 ∨ p2839)
    (h73502 : p3989 ∨ p2187)
    (h55933 : (¬ p2132) ∨ (¬ p2780) ∨ (¬ p3583) ∨ (¬ p3989) ∨ (¬ p4428))
    : p2774 ∨ (¬ p2132) ∨ p2839 ∨ (¬ p4428) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4428 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55933 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step90696 (p2132 p2753 p2829 p3688 p3985 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h5916 : (¬ p2132) ∨ (¬ p2753) ∨ (¬ p3688) ∨ (¬ p3985))
    : (¬ p2753) ∨ p2829 ∨ (¬ p2132) ∨ (¬ p3985) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2753 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3985 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h5916 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step90698 (p2098 p2104 p2132 p4744 : Prop)
    (h73204 : p2104 ∨ p2098)
    (h19765 : (¬ p2104) ∨ (¬ p2132) ∨ (¬ p4744))
    : (¬ p4744) ∨ p2098 ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4744 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h19765 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u0)))))))

theorem step90700 (p2132 p2707 p2839 p3246 p3583 p3589 p4344 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h43618 : (¬ p2132) ∨ (¬ p2707) ∨ (¬ p3246) ∨ (¬ p3583) ∨ (¬ p3589) ∨ (¬ p4344))
    : (¬ p2707) ∨ (¬ p3246) ∨ (¬ p4344) ∨ (¬ p3589) ∨ (¬ p2132) ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h43618 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step90703 (p2132 p2427 p2696 p2870 p3365 p4235 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h73536 : p4235 ∨ p2427)
    (h52712 : (¬ p2132) ∨ (¬ p2870) ∨ (¬ p3365) ∨ (¬ p4235))
    : (¬ p2870) ∨ p2696 ∨ (¬ p2132) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h52712 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step90704 (p2132 p2427 p2753 p2870 p3367 p3585 p4235 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73428 : p3585 ∨ p3367)
    (h46727 : (¬ p2132) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p3585) ∨ (¬ p4235))
    : (¬ p2870) ∨ p2427 ∨ p3367 ∨ (¬ p2753) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46727 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step90706 (p2132 p2696 p2870 p2901 p3365 p4320 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h73552 : p4320 ∨ p2901)
    (h43785 : (¬ p2132) ∨ (¬ p2870) ∨ (¬ p3365) ∨ (¬ p4320))
    : (¬ p2870) ∨ p2696 ∨ p2901 ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43785 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step90707 (p2132 p2252 p2573 p2579 p2655 p2750 p2753 p2870 p3016 p3246 p3343 p3359 p4022 p4625 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73388 : p3359 ∨ p3343)
    (h64549 : (¬ p2132) ∨ (¬ p2252) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p3016) ∨ (¬ p3246) ∨ (¬ p3359) ∨ (¬ p4022) ∨ (¬ p4625))
    : (¬ p2753) ∨ (¬ p4625) ∨ (¬ p4022) ∨ (¬ p2132) ∨ (¬ p2655) ∨ (¬ p3016) ∨ (¬ p2870) ∨ (¬ p2750) ∨ (¬ p2252) ∨ p2573 ∨ p3343 ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2753 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4022 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u13 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h64549 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u13))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u2))) (fun r10 => (False.elim (r10 u1)))))))))))))))))))))))))

theorem step90708 (p2132 p2696 p2870 p2881 p3365 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h47432 : (¬ p2132) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3365))
    : (¬ p2870) ∨ p2696 ∨ (¬ p2132) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47432 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90709 (p2132 p2870 p3389 p3540 p3905 p4647 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h62176 : (¬ p2132) ∨ (¬ p2870) ∨ (¬ p3540) ∨ (¬ p3905) ∨ (¬ p4647))
    : (¬ p3905) ∨ p3389 ∨ (¬ p4647) ∨ (¬ p2132) ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3905 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h62176 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step90710 (p2132 p2829 p2839 p3125 p3583 p4185 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h57966 : (¬ p2132) ∨ (¬ p2829) ∨ (¬ p3125) ∨ (¬ p3583) ∨ (¬ p4185))
    : (¬ p3125) ∨ p2839 ∨ (¬ p2132) ∨ (¬ p2829) ∨ (¬ p4185) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h57966 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step90711 (p2132 p2493 p2839 p3422 p3541 p3583 p3584 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73426 : p3584 ∨ p3422)
    (h45836 : (¬ p2132) ∨ (¬ p2493) ∨ (¬ p3541) ∨ (¬ p3583) ∨ (¬ p3584))
    : p2839 ∨ p3422 ∨ (¬ p2132) ∨ (¬ p3541) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2839) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45836 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step90712 (p2132 p2707 p2717 p2839 p3583 p3589 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h45841 : (¬ p2132) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p3583) ∨ (¬ p3589))
    : (¬ p2707) ∨ p2839 ∨ (¬ p2717) ∨ (¬ p3589) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45841 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step90714 (p2132 p2737 p2797 p2839 p3583 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h45228 : (¬ p2132) ∨ (¬ p2737) ∨ (¬ p2797) ∨ (¬ p3583))
    : (¬ p2797) ∨ p2839 ∨ (¬ p2132) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45228 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90715 (p2132 p2341 p2839 p2881 p3551 p3583 p3820 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73424 : p3583 ∨ p2839)
    (h43856 : (¬ p2132) ∨ (¬ p2881) ∨ (¬ p3551) ∨ (¬ p3583) ∨ (¬ p3820))
    : (¬ p3820) ∨ p2341 ∨ (¬ p2881) ∨ (¬ p2132) ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3820 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43856 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step90717 (p2132 p2753 p2839 p3583 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h5391 : (¬ p2132) ∨ (¬ p2753) ∨ (¬ p3583))
    : p2839 ∨ (¬ p2753) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2839) := (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h5391 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step90718 (p2132 p2774 p2780 p2870 p3096 p4342 p4558 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h50609 : (¬ p2132) ∨ (¬ p2780) ∨ (¬ p2870) ∨ (¬ p3096) ∨ (¬ p4342) ∨ (¬ p4558))
    : p2774 ∨ (¬ p2132) ∨ (¬ p2870) ∨ (¬ p3096) ∨ (¬ p4558) ∨ (¬ p4342) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4342 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h50609 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step90719 (p2132 p2598 p3054 p3055 : Prop)
    (h73350 : p3055 ∨ p2598)
    (h4235 : (¬ p2132) ∨ (¬ p3054) ∨ (¬ p3055))
    : (¬ p3054) ∨ (¬ p2132) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3054 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h4235 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u3)))))))

theorem step90721 (p2132 p2598 p3055 p3201 p3695 p3876 p4644 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73350 : p3055 ∨ p2598)
    (h51333 : (¬ p2132) ∨ (¬ p3055) ∨ (¬ p3695) ∨ (¬ p3876) ∨ (¬ p4644))
    : p3201 ∨ (¬ p2132) ∨ (¬ p3695) ∨ p2598 ∨ (¬ p4644) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h51333 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step90722 (p2132 p2598 p3055 p3641 p3695 p3874 p4608 : Prop)
    (h73484 : p3874 ∨ p3641)
    (h73350 : p3055 ∨ p2598)
    (h48365 : (¬ p2132) ∨ (¬ p3055) ∨ (¬ p3695) ∨ (¬ p3874) ∨ (¬ p4608))
    : (¬ p2132) ∨ p3641 ∨ p2598 ∨ (¬ p3695) ∨ (¬ p4608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48365 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step90723 (p2132 p2528 p2534 p2870 p3246 p3367 p3585 p3641 p3874 p3950 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73484 : p3874 ∨ p3641)
    (h73428 : p3585 ∨ p3367)
    (h71881 : (¬ p2534) ∨ (¬ p2132) ∨ (¬ p3246) ∨ (¬ p3874) ∨ (¬ p3950) ∨ (¬ p2870) ∨ (¬ p3585))
    : p2528 ∨ (¬ p3950) ∨ p3641 ∨ (¬ p2870) ∨ (¬ p2132) ∨ (¬ p3246) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h71881 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u9)))))))))))))))

theorem step90726 (p2132 p2245 p2427 p2807 p2870 p2992 p2996 p3027 p3414 p3662 p4235 p4705 p4733 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73340 : p3027 ∨ p2996)
    (h73440 : p3662 ∨ p2992)
    (h73392 : p3414 ∨ p2807)
    (h50920 : (¬ p2132) ∨ (¬ p2245) ∨ (¬ p2870) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p3662) ∨ (¬ p4235) ∨ (¬ p4705) ∨ (¬ p4733))
    : (¬ p2870) ∨ p2427 ∨ (¬ p2245) ∨ (¬ p4705) ∨ (¬ p4733) ∨ p2996 ∨ p2992 ∨ p2807 ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h50920 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step90728 (p2132 p2619 p2737 p2743 p2753 p3146 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h54457 : (¬ p2132) ∨ (¬ p2619) ∨ (¬ p2743) ∨ (¬ p2753) ∨ (¬ p3146))
    : (¬ p2753) ∨ (¬ p3146) ∨ p2737 ∨ (¬ p2132) ∨ (¬ p2619) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2753 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h54457 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step90731 (p2132 p2252 p2417 p2437 p2651 p2657 p2750 p2753 p2860 p3125 p3742 p4278 p4621 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73288 : p2657 ∨ p2651)
    (h73452 : p3742 ∨ p2437)
    (h63167 : (¬ p2132) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4621))
    : (¬ p2753) ∨ p2417 ∨ p2651 ∨ p2437 ∨ (¬ p2860) ∨ (¬ p2132) ∨ (¬ p3125) ∨ (¬ p2750) ∨ (¬ p4621) ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2753 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63167 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step90732 (p2132 p2252 p2651 p2657 p2750 p2753 p2870 p3276 p3343 p3359 p4129 p4425 p4826 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73388 : p3359 ∨ p3343)
    (h73288 : p2657 ∨ p2651)
    (h64511 : (¬ p2132) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p3359) ∨ (¬ p4129) ∨ (¬ p4425) ∨ (¬ p4826))
    : p3276 ∨ p3343 ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p4826) ∨ (¬ p4129) ∨ (¬ p2870) ∨ p2651 ∨ (¬ p2753) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4129 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64511 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step90735 (p2132 p2245 p2651 p2657 p2727 p2870 p2881 p3189 p4041 p4360 p4733 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73288 : p2657 ∨ p2651)
    (h50011 : (¬ p2132) ∨ (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p4041) ∨ (¬ p4360) ∨ (¬ p4733))
    : (¬ p2245) ∨ p3189 ∨ (¬ p2881) ∨ (¬ p4733) ∨ (¬ p2727) ∨ (¬ p4041) ∨ (¬ p2132) ∨ (¬ p2870) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h50011 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step90736 (p2132 p2696 p2839 p3365 p3367 p3583 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73390 : p3365 ∨ p2696)
    (h45344 : (¬ p2132) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3583))
    : p2839 ∨ (¬ p3367) ∨ (¬ p2132) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2839) := (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45344 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90737 (p2132 p2245 p2331 p2641 p2870 p2881 p2963 p3189 p4360 p4503 p4733 p4769 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73338 : p2963 ∨ p2331)
    (h62501 : (¬ p2132) ∨ (¬ p2245) ∨ (¬ p2641) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p2963) ∨ (¬ p4360) ∨ (¬ p4503) ∨ (¬ p4733) ∨ (¬ p4769))
    : (¬ p2641) ∨ p3189 ∨ (¬ p2881) ∨ (¬ p2870) ∨ (¬ p4769) ∨ (¬ p4733) ∨ (¬ p4503) ∨ (¬ p2245) ∨ (¬ p2132) ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4769 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h62501 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step90740 (p2132 p2241 p2247 p2641 p2668 p2870 p2881 p3324 p4154 p4503 p4733 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h73226 : p2247 ∨ p2241)
    (h73526 : p4154 ∨ p2641)
    (h64716 : (¬ p2132) ∨ (¬ p2247) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3324) ∨ (¬ p4154) ∨ (¬ p4503) ∨ (¬ p4733))
    : (¬ p2870) ∨ (¬ p2881) ∨ (¬ p4503) ∨ (¬ p4733) ∨ p2668 ∨ p2241 ∨ (¬ p2132) ∨ p2641 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64716 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step90755 (p2132 p2509 p2528 p2534 p2870 p3246 p3379 p3452 p3950 p4733 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73268 : p2534 ∨ p2528)
    (h51335 : (¬ p2132) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3452) ∨ (¬ p3950) ∨ (¬ p4733))
    : p3379 ∨ (¬ p4733) ∨ (¬ p2870) ∨ (¬ p2132) ∨ p2528 ∨ (¬ p3950) ∨ (¬ p3246) ∨ (¬ p2509) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51335 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step90764 (p2132 p2509 p2528 p2534 p2860 p3125 p3379 p3452 p4330 p4733 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73394 : p3452 ∨ p3379)
    (h57567 : (¬ p2132) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p3452) ∨ (¬ p4330) ∨ (¬ p4733))
    : (¬ p4733) ∨ (¬ p3125) ∨ p2528 ∨ (¬ p4330) ∨ (¬ p2509) ∨ p3379 ∨ (¬ p2860) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4733 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h57567 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step90765 (p2132 p2870 p3193 p3276 p3379 p3452 p4129 p4425 p4733 p4826 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73394 : p3452 ∨ p3379)
    (h52626 : (¬ p2132) ∨ (¬ p2870) ∨ (¬ p3193) ∨ (¬ p3452) ∨ (¬ p4129) ∨ (¬ p4425) ∨ (¬ p4733) ∨ (¬ p4826))
    : (¬ p3193) ∨ p3276 ∨ (¬ p4129) ∨ (¬ p4826) ∨ (¬ p2870) ∨ p3379 ∨ (¬ p4733) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3193 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4129 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h52626 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step90766 (p2132 p2406 p2598 p3055 p3238 p3695 p5214 : Prop)
    (h73350 : p3055 ∨ p2598)
    (h73374 : p3238 ∨ p2406)
    (h41137 : (¬ p2132) ∨ (¬ p3055) ∨ (¬ p3238) ∨ (¬ p3695) ∨ (¬ p5214))
    : (¬ p3695) ∨ (¬ p2132) ∨ (¬ p5214) ∨ p2598 ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3695 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5214 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41137 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step90770 (p2132 p2187 p2241 p2750 p2753 p2860 p3093 p3309 p3549 p3591 p4405 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73406 : p3549 ∨ p3309)
    (h56541 : (¬ p2132) ∨ (¬ p2187) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2860) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4405))
    : p3093 ∨ (¬ p2241) ∨ (¬ p4405) ∨ (¬ p2187) ∨ (¬ p2750) ∨ (¬ p2860) ∨ (¬ p2132) ∨ p3309 ∨ (¬ p2753) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h56541 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step90771 (p2132 p2187 p2459 p2860 p3073 p3449 p3860 p4133 p4261 p4733 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h73544 : p4261 ∨ p3073)
    (h51485 : (¬ p2132) ∨ (¬ p2187) ∨ (¬ p2459) ∨ (¬ p2860) ∨ (¬ p3860) ∨ (¬ p4133) ∨ (¬ p4261) ∨ (¬ p4733))
    : (¬ p2132) ∨ p3449 ∨ (¬ p4733) ∨ (¬ p4133) ∨ (¬ p2459) ∨ p3073 ∨ (¬ p2860) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h51485 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step90773 (p2132 p2528 p2870 p2881 p3073 p3379 p3452 p3453 p4261 p4438 p4733 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h73394 : p3452 ∨ p3379)
    (h55056 : (¬ p2132) ∨ (¬ p2528) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3452) ∨ (¬ p3453) ∨ (¬ p4261) ∨ (¬ p4438) ∨ (¬ p4733))
    : p3073 ∨ (¬ p4733) ∨ (¬ p2870) ∨ (¬ p2132) ∨ p3379 ∨ (¬ p3453) ∨ (¬ p4438) ∨ (¬ p2528) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3453 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55056 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step90775 (p2132 p2177 p2241 p2247 p2449 p2870 p2996 p3947 p4140 p4666 p4733 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73494 : p3947 ∨ p2449)
    (h61981 : (¬ p2132) ∨ (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2870) ∨ (¬ p2996) ∨ (¬ p3947) ∨ (¬ p4140) ∨ (¬ p4666) ∨ (¬ p4733))
    : (¬ p2996) ∨ (¬ p4140) ∨ (¬ p2177) ∨ p2241 ∨ (¬ p4733) ∨ (¬ p2132) ∨ (¬ p2870) ∨ p2449 ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h61981 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step90776 (p2132 p2264 p2663 p2737 p2743 p2891 p3246 p3361 p3389 p3540 p3553 p3579 p4418 p4668 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73410 : p3553 ∨ p2264)
    (h73402 : p3540 ∨ p3389)
    (h71885 : p2663 ∨ (¬ p4418) ∨ (¬ p3246) ∨ (¬ p2891) ∨ (¬ p2743) ∨ (¬ p4668) ∨ (¬ p3540) ∨ (¬ p3579) ∨ (¬ p2132) ∨ (¬ p3361) ∨ (¬ p3553))
    : p2663 ∨ p2737 ∨ (¬ p3361) ∨ (¬ p2132) ∨ p2264 ∨ (¬ p2891) ∨ (¬ p4418) ∨ (¬ p3246) ∨ p3389 ∨ (¬ p3579) ∨ (¬ p4668) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2663) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u13 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h71885 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (False.elim (r9 u12)))))))))))))))))))))))

theorem step90779 (p2132 p2241 p2247 p2870 p3189 p3246 p3256 p3950 p4118 p4360 p4733 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73520 : p4118 ∨ p3256)
    (h73226 : p2247 ∨ p2241)
    (h50461 : (¬ p2132) ∨ (¬ p2247) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p4733))
    : p3189 ∨ p3256 ∨ (¬ p2870) ∨ (¬ p3246) ∨ p2241 ∨ (¬ p4733) ∨ (¬ p3950) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50461 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step90781 (p2132 p2241 p2247 p2860 p3125 p3189 p3256 p4118 p4330 p4360 p4733 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h73226 : p2247 ∨ p2241)
    (h73566 : p4360 ∨ p3189)
    (h49254 : (¬ p2132) ∨ (¬ p2247) ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p4118) ∨ (¬ p4330) ∨ (¬ p4360) ∨ (¬ p4733))
    : p3256 ∨ p2241 ∨ (¬ p3125) ∨ (¬ p4330) ∨ (¬ p2132) ∨ p3189 ∨ (¬ p4733) ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h49254 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step90785 (p2098 p2104 p2132 p2860 p4312 p4963 : Prop)
    (h73204 : p2104 ∨ p2098)
    (h69522 : (¬ p2104) ∨ (¬ p4963) ∨ (¬ p2860) ∨ (¬ p4312) ∨ (¬ p2132))
    : (¬ p4963) ∨ p2098 ∨ (¬ p2860) ∨ (¬ p2132) ∨ (¬ p4312) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4963 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h69522 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step90786 (p2132 p2619 p2696 p3156 p3365 p3497 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h73390 : p3365 ∨ p2696)
    (h60974 : (¬ p2132) ∨ (¬ p2619) ∨ (¬ p3365) ∨ (¬ p3497))
    : (¬ p2132) ∨ (¬ p2619) ∨ p3156 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60974 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90789 (p2132 p2274 p2829 p2839 p3583 p3589 p4185 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h42800 : (¬ p2132) ∨ (¬ p2274) ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p3589) ∨ (¬ p4185))
    : (¬ p2829) ∨ p2839 ∨ (¬ p3589) ∨ (¬ p2274) ∨ (¬ p2132) ∨ (¬ p4185) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42800 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step90791 (p2132 p3105 p3266 p3680 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h65096 : (¬ p2132) ∨ (¬ p3105) ∨ (¬ p3680) ∨ (¬ p4444))
    : p3266 ∨ (¬ p3680) ∨ (¬ p2132) ∨ (¬ p3105) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h65096 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90792 (p2132 p2166 p2533 p3266 p3680 p4418 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h63391 : (¬ p2132) ∨ (¬ p2166) ∨ (¬ p2533) ∨ (¬ p3680) ∨ (¬ p4418) ∨ (¬ p4444))
    : p3266 ∨ (¬ p4418) ∨ (¬ p3680) ∨ (¬ p2166) ∨ (¬ p2132) ∨ (¬ p2533) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h63391 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step90793 (p2132 p2252 p2750 p2753 p2870 p3166 p3172 p3256 p3266 p4118 p4129 p4444 p4826 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h73580 : p4444 ∨ p3266)
    (h73356 : p3172 ∨ p3166)
    (h64528 : (¬ p2132) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4129) ∨ (¬ p4444) ∨ (¬ p4826))
    : (¬ p4129) ∨ (¬ p2753) ∨ p3256 ∨ (¬ p2252) ∨ (¬ p2750) ∨ p3266 ∨ (¬ p2870) ∨ (¬ p2132) ∨ (¬ p4826) ∨ p3166 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4129 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h64528 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step90797 (p2122 p2132 p2829 p2839 p3583 p3589 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h45834 : (¬ p2122) ∨ (¬ p2132) ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p3589))
    : (¬ p2829) ∨ p2839 ∨ (¬ p2132) ∨ (¬ p2122) ∨ (¬ p3589) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45834 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step90798 (p2132 p2341 p2742 p3038 p3527 p3551 p3820 p5052 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h56991 : (¬ p2132) ∨ (¬ p2742) ∨ (¬ p3038) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p5052))
    : (¬ p3527) ∨ (¬ p3820) ∨ (¬ p3038) ∨ (¬ p5052) ∨ (¬ p2742) ∨ p2341 ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3820 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3038 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5052 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h56991 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step90800 (p2122 p2132 p2839 p3309 p3583 p3589 p3822 p4869 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73472 : p3822 ∨ p2122)
    (h45843 : (¬ p2132) ∨ (¬ p3309) ∨ (¬ p3583) ∨ (¬ p3589) ∨ (¬ p3822) ∨ (¬ p4869))
    : (¬ p3309) ∨ (¬ p4869) ∨ p2839 ∨ p2122 ∨ (¬ p2132) ∨ (¬ p3589) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4869 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45843 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step90801 (p2132 p2307 p2313 p2742 p2778 p3309 p4759 p5052 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h51296 : (¬ p2132) ∨ (¬ p2313) ∨ (¬ p2742) ∨ (¬ p2778) ∨ (¬ p3309) ∨ (¬ p4759) ∨ (¬ p5052))
    : (¬ p3309) ∨ (¬ p2742) ∨ (¬ p5052) ∨ (¬ p4759) ∨ (¬ p2778) ∨ p2307 ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5052 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h51296 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step90802 (p2132 p2166 p2191 p2619 p4874 : Prop)
    (h73222 : p2191 ∨ p2166)
    (h71887 : (¬ p2619) ∨ (¬ p2191) ∨ (¬ p4874) ∨ (¬ p2132))
    : (¬ p2619) ∨ (¬ p2132) ∨ p2166 ∨ (¬ p4874) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2166) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2191 := (Or.elim h73222 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h71887 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step90804 (p2132 p2187 p2753 p2860 p3367 p3585 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h45779 : (¬ p2132) ∨ (¬ p2187) ∨ (¬ p2753) ∨ (¬ p2860) ∨ (¬ p3585))
    : (¬ p2132) ∨ (¬ p2753) ∨ (¬ p2860) ∨ (¬ p2187) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45779 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step90806 (p2098 p2104 p2132 p2166 p4740 p4960 p5051 : Prop)
    (h73204 : p2104 ∨ p2098)
    (h48086 : (¬ p2104) ∨ (¬ p2132) ∨ (¬ p2166) ∨ (¬ p4740) ∨ (¬ p4960) ∨ (¬ p5051))
    : p2098 ∨ (¬ p5051) ∨ (¬ p2166) ∨ (¬ p2132) ∨ (¬ p4740) ∨ (¬ p4960) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : p5051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48086 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step90807 (p2098 p2104 p2132 p2839 p3146 p3583 p3692 p4740 : Prop)
    (h73204 : p2104 ∨ p2098)
    (h73448 : p3692 ∨ p3146)
    (h73424 : p3583 ∨ p2839)
    (h43163 : (¬ p2104) ∨ (¬ p2132) ∨ (¬ p3583) ∨ (¬ p3692) ∨ (¬ p4740))
    : p2098 ∨ p3146 ∨ p2839 ∨ (¬ p4740) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43163 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step90808 (p2122 p2132 p2307 p2313 p2778 p4426 p5052 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h59057 : (¬ p2122) ∨ (¬ p2132) ∨ (¬ p2313) ∨ (¬ p2778) ∨ (¬ p4426) ∨ (¬ p5052))
    : (¬ p2778) ∨ p2307 ∨ (¬ p5052) ∨ (¬ p2122) ∨ (¬ p2132) ∨ (¬ p4426) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2778 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5052 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h59057 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step90810 (p2122 p2132 p2396 p2753 p3073 p3379 p3449 p3860 p3950 p3985 p4261 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h73544 : p4261 ∨ p3073)
    (h71889 : (¬ p2396) ∨ (¬ p3950) ∨ (¬ p3379) ∨ (¬ p2132) ∨ (¬ p2753) ∨ (¬ p2122) ∨ (¬ p4261) ∨ (¬ p3860) ∨ (¬ p3985))
    : (¬ p2122) ∨ (¬ p2396) ∨ (¬ p2132) ∨ (¬ p3950) ∨ (¬ p3985) ∨ p3449 ∨ p3073 ∨ (¬ p3379) ∨ (¬ p2753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3985 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h71889 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step90812 (p2088 p2102 p3073 p3425 p3471 p3857 p3918 p3985 p4313 p4317 p4782 : Prop)
    (h73396 : p3471 ∨ p3425)
    (h73480 : p3857 ∨ p2088)
    (h55924 : (¬ p2102) ∨ (¬ p3073) ∨ (¬ p3471) ∨ (¬ p3857) ∨ (¬ p3918) ∨ (¬ p3985) ∨ (¬ p4313) ∨ (¬ p4317) ∨ (¬ p4782))
    : (¬ p4317) ∨ (¬ p3073) ∨ p3425 ∨ (¬ p3918) ∨ (¬ p3985) ∨ (¬ p2102) ∨ (¬ p4782) ∨ p2088 ∨ (¬ p4313) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4317 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3918 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3985 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2102 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4782 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h55924 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step90822 (p2230 p2246 p2383 p2589 p2668 p2744 p2870 p3246 p3323 p3324 p3366 p3690 p3695 p3905 p3987 p4244 p4621 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h73446 : p3690 ∨ p3246)
    (h73284 : p2589 ∨ p2230)
    (h73540 : p4244 ∨ p2870)
    (h59421 : (¬ p2246) ∨ (¬ p2383) ∨ (¬ p2589) ∨ (¬ p2744) ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p3366) ∨ (¬ p3690) ∨ (¬ p3695) ∨ (¬ p3905) ∨ (¬ p3987) ∨ (¬ p4244) ∨ (¬ p4621))
    : (¬ p3323) ∨ (¬ p2383) ∨ (¬ p4621) ∨ p2668 ∨ (¬ p3987) ∨ (¬ p2246) ∨ p3246 ∨ (¬ p2744) ∨ p2230 ∨ (¬ p3366) ∨ p2870 ∨ (¬ p3695) ∨ (¬ p3905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u14 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u15 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u16 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h59421 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u15))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u14))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u4))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u16))) (fun r11 => (False.elim (r11 u2)))))))))))))))))))))))))))

theorem step90825 (p2177 p2264 p2299 p2307 p2313 p4156 p4581 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h73238 : p2313 ∨ p2307)
    (h49216 : (¬ p2264) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p4156) ∨ (¬ p4581))
    : (¬ p2264) ∨ (¬ p4156) ∨ p2177 ∨ (¬ p4581) ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49216 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step90826 (p2331 p2807 p2963 p3414 p4156 : Prop)
    (h73337 : (¬ p2331) ∨ (¬ p2963))
    (h73392 : p3414 ∨ p2807)
    (h6677 : p2963 ∨ (¬ p3414) ∨ (¬ p4156))
    : (¬ p4156) ∨ (¬ p2331) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2963) := (Or.elim h73337 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u4 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h6677 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u0)))))))

theorem step90832 (p2264 p2881 p3323 p3570 p4037 p4140 p4156 p4620 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73508 : p4037 ∨ p3323)
    (h41122 : (¬ p2264) ∨ (¬ p3570) ∨ (¬ p4037) ∨ (¬ p4140) ∨ (¬ p4156) ∨ (¬ p4620))
    : (¬ p4156) ∨ (¬ p4140) ∨ (¬ p2264) ∨ p2881 ∨ p3323 ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41122 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step90833 (p2668 p3324 p3931 p4156 p4260 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h71890 : (¬ p3931) ∨ (¬ p3324) ∨ (¬ p4260) ∨ (¬ p4156))
    : (¬ p4260) ∨ (¬ p3931) ∨ p2668 ∨ (¬ p4156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4260 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h71890 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step90836 (p2177 p2241 p2264 p2299 p2641 p4156 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h43427 : (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2299) ∨ (¬ p2641) ∨ (¬ p4156))
    : (¬ p2264) ∨ (¬ p2641) ∨ p2177 ∨ (¬ p4156) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43427 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step90839 (p2396 p2449 p2668 p3324 p4107 p4156 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h73514 : p4107 ∨ p2396)
    (h71891 : (¬ p2449) ∨ (¬ p3324) ∨ (¬ p4156) ∨ (¬ p4107))
    : (¬ p2449) ∨ (¬ p4156) ∨ p2668 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71891 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step90849 (p2274 p4275 p5818 : Prop)
    (h74101 : p2274 ∨ (¬ p5818))
    (h11905 : p4275 ∨ p5818)
    : p4275 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4275) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5818) := (Or.elim h74101 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11905 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step90850 (p2427 p4235 p4647 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h42697 : (¬ p4235) ∨ p4647)
    : p2427 ∨ p4647 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2427) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4647) := (fun h => hn (Or.inr h));
    let u2 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42697 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step90851 (p2210 p2427 p2563 p2891 p4235 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h45246 : (¬ p2210) ∨ (¬ p2563) ∨ (¬ p2891) ∨ (¬ p4235))
    : (¬ p2891) ∨ p2427 ∨ (¬ p2210) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45246 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90852 (p2177 p2284 p2299 p2427 p2563 p3952 p4235 p4275 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73496 : p3952 ∨ p2284)
    (h73234 : p2299 ∨ p2177)
    (h48545 : (¬ p2299) ∨ (¬ p2563) ∨ (¬ p3952) ∨ (¬ p4235) ∨ (¬ p4275))
    : p2427 ∨ p2284 ∨ (¬ p4275) ∨ (¬ p2563) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2427) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48545 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step90853 (p2295 p2427 p2563 p4235 p4275 p4560 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h72955 : p4560)
    (h62626 : (¬ p2295) ∨ (¬ p2563) ∨ (¬ p4235) ∨ (¬ p4275) ∨ (¬ p4560))
    : (¬ p2295) ∨ p2427 ∨ (¬ p2563) ∨ (¬ p4275) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4560 := h72955;
    (Or.elim h62626 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step90854 (p2427 p2470 p2476 p2563 p3051 p4235 p4399 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73250 : p2476 ∨ p2470)
    (h50921 : (¬ p2476) ∨ (¬ p2563) ∨ (¬ p3051) ∨ (¬ p4235) ∨ (¬ p4399))
    : (¬ p3051) ∨ (¬ p4399) ∨ p2427 ∨ (¬ p2563) ∨ p2470 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50921 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step90855 (p2220 p2427 p2563 p3051 p4120 p4235 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h73536 : p4235 ∨ p2427)
    (h69523 : (¬ p4120) ∨ (¬ p3051) ∨ (¬ p4235) ∨ (¬ p2563))
    : (¬ p3051) ∨ p2220 ∨ (¬ p2563) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69523 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step90856 (p2144 p2427 p2563 p2598 p3051 p3055 p4235 : Prop)
    (h73350 : p3055 ∨ p2598)
    (h73536 : p4235 ∨ p2427)
    (h46761 : (¬ p2144) ∨ (¬ p2563) ∨ (¬ p3051) ∨ (¬ p3055) ∨ (¬ p4235))
    : (¬ p3051) ∨ (¬ p2144) ∨ (¬ p2563) ∨ p2598 ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46761 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step90860 (p2427 p2563 p3051 p3125 p4235 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h46567 : (¬ p2563) ∨ (¬ p3051) ∨ (¬ p3125) ∨ (¬ p4235))
    : (¬ p3125) ∨ (¬ p3051) ∨ p2427 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46567 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90861 (p2427 p2563 p3125 p3323 p4037 p4235 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73536 : p4235 ∨ p2427)
    (h55090 : (¬ p2563) ∨ (¬ p3125) ∨ (¬ p4037) ∨ (¬ p4235))
    : (¬ p3125) ∨ p3323 ∨ p2427 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h55090 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step90865 (p2427 p2563 p2901 p2946 p4235 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h46560 : (¬ p2563) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p4235))
    : p2427 ∨ (¬ p2946) ∨ (¬ p2563) ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2427) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h46560 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90869 (p2427 p2563 p3872 p4235 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h20497 : (¬ p2563) ∨ (¬ p3872) ∨ (¬ p4235))
    : p2427 ∨ (¬ p3872) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2427) := (fun h => hn (Or.inl h));
    let u1 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h20497 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step90871 (p2098 p2104 p2139 p2363 p2373 p2427 p3051 p3609 p4235 p4340 p4433 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h73536 : p4235 ∨ p2427)
    (h73204 : p2104 ∨ p2098)
    (h62681 : (¬ p2104) ∨ (¬ p2139) ∨ (¬ p2363) ∨ (¬ p2373) ∨ (¬ p3051) ∨ (¬ p4235) ∨ (¬ p4340) ∨ (¬ p4433))
    : (¬ p3051) ∨ p3609 ∨ (¬ p4433) ∨ (¬ p2363) ∨ p2427 ∨ p2098 ∨ (¬ p2139) ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h62681 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step90874 (p2187 p2427 p2563 p3051 p4235 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h46760 : (¬ p2187) ∨ (¬ p2563) ∨ (¬ p3051) ∨ (¬ p4235))
    : p2427 ∨ (¬ p2563) ∨ (¬ p3051) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2427) := (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h46760 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90876 (p2156 p2427 p2563 p2957 p2992 p3646 p3662 p4235 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73440 : p3662 ∨ p2992)
    (h73436 : p3646 ∨ p2156)
    (h60365 : (¬ p2563) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3662) ∨ (¬ p4235))
    : p2427 ∨ (¬ p2957) ∨ (¬ p2563) ∨ p2992 ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2427) := (fun h => hn (Or.inl h));
    let u1 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h60365 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step90879 (p2427 p2651 p2881 p2946 p2952 p3570 p3879 p4235 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73536 : p4235 ∨ p2427)
    (h73418 : p3570 ∨ p2881)
    (h60186 : (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3570) ∨ (¬ p3879) ∨ (¬ p4235))
    : p2946 ∨ p2427 ∨ p2881 ∨ (¬ p3879) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h60186 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step90880 (p2427 p2630 p2651 p2810 p2946 p2952 p3879 p4235 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73536 : p4235 ∨ p2427)
    (h73316 : p2810 ∨ p2630)
    (h42669 : (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2952) ∨ (¬ p3879) ∨ (¬ p4235))
    : p2946 ∨ (¬ p3879) ∨ (¬ p2651) ∨ p2427 ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42669 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step90883 (p2156 p2427 p3872 p4109 p4235 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h30491 : (¬ p2156) ∨ (¬ p3872) ∨ (¬ p4109) ∨ (¬ p4235))
    : (¬ p2156) ∨ p2427 ∨ (¬ p4109) ∨ (¬ p3872) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h30491 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90885 (p2177 p2406 p2427 p2881 p3238 p3570 p4235 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73536 : p4235 ∨ p2427)
    (h73374 : p3238 ∨ p2406)
    (h43954 : (¬ p2177) ∨ (¬ p3238) ∨ (¬ p3570) ∨ (¬ p4235))
    : p2881 ∨ p2427 ∨ (¬ p2177) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43954 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step90886 (p2307 p2427 p2563 p4235 p4275 p4489 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h49388 : (¬ p2307) ∨ (¬ p2563) ∨ (¬ p4235) ∨ (¬ p4275) ∨ (¬ p4489))
    : p2427 ∨ (¬ p2307) ∨ (¬ p4275) ∨ (¬ p2563) ∨ (¬ p4489) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2427) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4489 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49388 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step90893 (p2156 p2427 p2440 p3051 p3646 p4235 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73436 : p3646 ∨ p2156)
    (h42962 : (¬ p2440) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4235))
    : (¬ p3051) ∨ p2427 ∨ (¬ p2440) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42962 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90894 (p2156 p2284 p2427 p3051 p3646 p4235 p4705 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73436 : p3646 ∨ p2156)
    (h58881 : (¬ p2284) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4235) ∨ (¬ p4705))
    : (¬ p3051) ∨ (¬ p2284) ∨ p2427 ∨ (¬ p4705) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h58881 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step90896 (p2156 p2427 p2563 p2630 p2662 p2810 p3646 p3904 p4235 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73436 : p3646 ∨ p2156)
    (h73316 : p2810 ∨ p2630)
    (h46005 : (¬ p2563) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4235))
    : p2427 ∨ (¬ p2662) ∨ (¬ p3904) ∨ p2156 ∨ (¬ p2563) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2427) := (fun h => hn (Or.inl h));
    let u1 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h46005 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step90898 (p2427 p3146 p3256 p3692 p4119 p4235 p4237 p4705 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73536 : p4235 ∨ p2427)
    (h62314 : (¬ p3256) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4235) ∨ (¬ p4237) ∨ (¬ p4705))
    : (¬ p3256) ∨ p3146 ∨ p2427 ∨ (¬ p4705) ∨ (¬ p4119) ∨ (¬ p4237) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4237 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h62314 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step90900 (p2427 p2459 p2982 p3146 p4235 p4348 p4905 p5057 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73898 : p5057 ∨ (¬ p3146))
    (h73562 : p4348 ∨ p2459)
    (h67084 : (¬ p5057) ∨ (¬ p2982) ∨ (¬ p4235) ∨ (¬ p4905) ∨ (¬ p4348))
    : (¬ p2982) ∨ (¬ p4905) ∨ p2427 ∨ (¬ p3146) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p5057 := (Or.elim h73898 (fun q0 => q0) (fun r0 => (False.elim (r0 u3))));
    let u7 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h67084 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step90904 (p2881 p2901 p2911 p3644 p4705 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h66806 : (¬ p3644) ∨ (¬ p2881) ∨ (¬ p4705) ∨ (¬ p2901))
    : (¬ p2901) ∨ p2911 ∨ (¬ p4705) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2911) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66806 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step90905 (p2563 p3323 p3654 p3946 p4110 p4336 p4356 p4705 : Prop)
    (h73492 : p3946 ∨ p3654)
    (h73516 : p4110 ∨ p2563)
    (h42038 : (¬ p3323) ∨ (¬ p3946) ∨ (¬ p4110) ∨ (¬ p4336) ∨ (¬ p4356) ∨ (¬ p4705))
    : (¬ p3323) ∨ p3654 ∨ (¬ p4705) ∨ (¬ p4356) ∨ (¬ p4336) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3654) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h42038 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step90909 (p2417 p2441 p2901 p3246 p4278 p4705 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h54204 : (¬ p2441) ∨ (¬ p2901) ∨ (¬ p3246) ∨ (¬ p4278) ∨ (¬ p4705))
    : p2417 ∨ (¬ p3246) ∨ (¬ p2901) ∨ (¬ p4705) ∨ (¬ p2441) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h54204 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step90910 (p2187 p2284 p2352 p2590 p3956 p4705 : Prop)
    (h73500 : p3956 ∨ p2352)
    (h62327 : (¬ p2187) ∨ (¬ p2284) ∨ (¬ p2590) ∨ (¬ p3956) ∨ (¬ p4705))
    : (¬ p2187) ∨ p2352 ∨ (¬ p2284) ∨ (¬ p4705) ∨ (¬ p2590) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2352) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h62327 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step90911 (p2797 p4337 p4840 : Prop)
    (h73786 : p4840 ∨ p2797)
    (h7946 : p4337 ∨ (¬ p4840))
    : p4337 ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4337) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr h));
    let u2 : p4840 := (Or.elim h73786 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h7946 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step90912 (p2797 p4337 p5917 : Prop)
    (h74229 : p2797 ∨ (¬ p5917))
    (h12485 : p4337 ∨ p5917)
    : p4337 ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4337) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5917) := (Or.elim h74229 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12485 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step90915 (p3425 p5256 p5257 : Prop)
    (h73980 : p5256 ∨ (¬ p3425))
    (h8946 : (¬ p5256) ∨ p5257)
    : (¬ p3425) ∨ p5257 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3425 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5257) := (fun h => hn (Or.inr h));
    let u2 : p5256 := (Or.elim h73980 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h8946 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step90918 (p2274 p2307 p2313 p3564 p3654 p4137 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h73238 : p2313 ∨ p2307)
    (h43356 : (¬ p2274) ∨ (¬ p2313) ∨ (¬ p3654) ∨ (¬ p4137))
    : (¬ p3654) ∨ p3564 ∨ (¬ p2274) ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43356 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90921 (p2307 p2313 p3654 p4025 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h22149 : (¬ p2313) ∨ (¬ p3654) ∨ (¬ p4025))
    : (¬ p3654) ∨ p2307 ∨ (¬ p4025) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4025 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h22149 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u2)))))))

theorem step90923 (p2177 p2299 p2307 p2313 p3323 p3654 p4037 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73234 : p2299 ∨ p2177)
    (h73508 : p4037 ∨ p3323)
    (h44366 : (¬ p2299) ∨ (¬ p2313) ∨ (¬ p3654) ∨ (¬ p4037))
    : (¬ p3654) ∨ p2307 ∨ p2177 ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44366 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step90926 (p2187 p2383 p2387 p3564 p3654 p4137 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h73524 : p4137 ∨ p3564)
    (h43152 : (¬ p2187) ∨ (¬ p2387) ∨ (¬ p3654) ∨ (¬ p4137))
    : (¬ p3654) ∨ (¬ p2187) ∨ p2383 ∨ p3564 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43152 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step90927 (p2383 p2387 p2459 p3654 p4345 p4348 p4503 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h73562 : p4348 ∨ p2459)
    (h54038 : (¬ p2387) ∨ (¬ p3654) ∨ (¬ p4345) ∨ (¬ p4348) ∨ (¬ p4503))
    : (¬ p3654) ∨ (¬ p4503) ∨ (¬ p4345) ∨ p2383 ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4345 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54038 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step90928 (p2307 p2313 p3246 p3654 p3690 p4556 p4623 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73446 : p3690 ∨ p3246)
    (h49436 : (¬ p2313) ∨ (¬ p3654) ∨ (¬ p3690) ∨ (¬ p4556) ∨ (¬ p4623))
    : (¬ p4623) ∨ p2307 ∨ (¬ p3654) ∨ p3246 ∨ (¬ p4556) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4623 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49436 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step90929 (p2383 p2387 p3146 p3654 p3692 p4345 p4433 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73246 : p2387 ∨ p2383)
    (h41181 : (¬ p2387) ∨ (¬ p3654) ∨ (¬ p3692) ∨ (¬ p4345) ∨ (¬ p4433))
    : (¬ p3654) ∨ p3146 ∨ (¬ p4433) ∨ (¬ p4345) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4345 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41181 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step90930 (p2177 p2264 p2299 p2962 p3323 p3654 p4037 p4156 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73234 : p2299 ∨ p2177)
    (h45733 : (¬ p2264) ∨ (¬ p2299) ∨ (¬ p2962) ∨ (¬ p3654) ∨ (¬ p4037) ∨ (¬ p4156))
    : (¬ p3654) ∨ p3323 ∨ (¬ p4156) ∨ p2177 ∨ (¬ p2264) ∨ (¬ p2962) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45733 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step90931 (p2307 p2313 p2417 p3654 p4276 p4278 p4623 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73546 : p4278 ∨ p2417)
    (h41216 : (¬ p2313) ∨ (¬ p3654) ∨ (¬ p4276) ∨ (¬ p4278) ∨ (¬ p4623))
    : (¬ p4623) ∨ p2307 ∨ p2417 ∨ (¬ p3654) ∨ (¬ p4276) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4623 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41216 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step90936 (p2307 p2313 p2553 p2761 p3654 p4623 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h52428 : (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2761) ∨ (¬ p3654) ∨ (¬ p4623))
    : (¬ p3654) ∨ p2307 ∨ (¬ p4623) ∨ (¬ p2553) ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4623 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h52428 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step90944 (p2383 p2696 p2786 p2819 p3365 p4358 p4845 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h73390 : p3365 ∨ p2696)
    (h42028 : (¬ p2383) ∨ (¬ p2786) ∨ (¬ p3365) ∨ (¬ p4358) ∨ (¬ p4845))
    : (¬ p2383) ∨ p2819 ∨ (¬ p2786) ∨ p2696 ∨ (¬ p4845) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4845 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42028 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step90947 (p2122 p2383 p2598 p2786 p3055 p3923 p4024 : Prop)
    (h73350 : p3055 ∨ p2598)
    (h46907 : (¬ p2122) ∨ (¬ p2383) ∨ (¬ p2786) ∨ (¬ p3055) ∨ (¬ p3923) ∨ (¬ p4024))
    : (¬ p2383) ∨ (¬ p2122) ∨ p2598 ∨ (¬ p2786) ∨ (¬ p3923) ∨ (¬ p4024) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4024 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46907 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step90952 (p2177 p2406 p2911 p2922 p2928 p3644 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73320 : p2928 ∨ p2922)
    (h63845 : (¬ p2177) ∨ (¬ p2406) ∨ (¬ p2928) ∨ (¬ p3644))
    : p2911 ∨ (¬ p2406) ∨ (¬ p2177) ∨ p2922 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63845 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90953 (p2406 p2881 p2911 p2922 p2928 p3644 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73320 : p2928 ∨ p2922)
    (h52381 : (¬ p2406) ∨ (¬ p2881) ∨ (¬ p2928) ∨ (¬ p3644))
    : p2911 ∨ (¬ p2406) ∨ p2922 ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52381 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90955 (p2230 p2406 p2493 p2499 p2589 p3389 p4711 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h73260 : p2499 ∨ p2493)
    (h55288 : (¬ p2406) ∨ (¬ p2499) ∨ (¬ p2589) ∨ (¬ p3389) ∨ (¬ p4711))
    : (¬ p3389) ∨ (¬ p2406) ∨ p2230 ∨ p2493 ∨ (¬ p4711) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4711 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55288 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step90956 (p2406 p2493 p2499 p3323 p3564 p4137 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h73260 : p2499 ∨ p2493)
    (h45252 : (¬ p2406) ∨ (¬ p2499) ∨ (¬ p3323) ∨ (¬ p4137))
    : (¬ p2406) ∨ (¬ p3323) ∨ p3564 ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45252 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90958 (p2363 p2383 p2387 p2406 p2598 p2785 p2829 p2982 p3590 p3688 p4347 p4450 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73444 : p3688 ∨ p2829)
    (h73246 : p2387 ∨ p2383)
    (h71898 : (¬ p2982) ∨ (¬ p2406) ∨ (¬ p2598) ∨ (¬ p3688) ∨ (¬ p3590) ∨ (¬ p2387) ∨ (¬ p2785) ∨ (¬ p4450) ∨ (¬ p4347))
    : p2363 ∨ (¬ p3590) ∨ (¬ p2785) ∨ (¬ p2982) ∨ (¬ p2406) ∨ p2829 ∨ p2383 ∨ (¬ p4450) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h71898 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step90960 (p2284 p2386 p2406 p2493 p2499 p3743 p4705 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h54371 : (¬ p2284) ∨ (¬ p2386) ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p3743) ∨ (¬ p4705))
    : (¬ p2406) ∨ (¬ p2284) ∨ (¬ p4705) ∨ (¬ p3743) ∨ p2493 ∨ (¬ p2386) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54371 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step90962 (p2274 p2307 p2313 p2386 p2406 p2493 p2499 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73238 : p2313 ∨ p2307)
    (h45966 : (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p2406) ∨ (¬ p2499))
    : (¬ p2406) ∨ (¬ p2274) ∨ (¬ p2386) ∨ p2493 ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45966 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step90965 (p2373 p2406 p2493 p2499 p2573 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h57764 : (¬ p2373) ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p2573))
    : (¬ p2406) ∨ p2493 ∨ (¬ p2373) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2493) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h57764 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step90968 (p2230 p2406 p2553 p2573 p2589 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h64011 : (¬ p2406) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2589))
    : (¬ p2406) ∨ (¬ p2553) ∨ (¬ p2573) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h64011 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90969 (p2187 p2406 p3125 p3193 p3989 p4022 p4138 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h46072 : (¬ p2406) ∨ (¬ p3125) ∨ (¬ p3193) ∨ (¬ p3989) ∨ (¬ p4022) ∨ (¬ p4138))
    : (¬ p3193) ∨ (¬ p3125) ∨ (¬ p2406) ∨ p2187 ∨ (¬ p4022) ∨ (¬ p4138) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3193 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4022 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46072 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step90971 (p2295 p2406 p2493 p2499 p2553 p2588 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73260 : p2499 ∨ p2493)
    (h56388 : (¬ p2295) ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p2588))
    : (¬ p2406) ∨ (¬ p2295) ∨ p2553 ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56388 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90972 (p2177 p2254 p2295 p2299 p2331 p2373 p2406 p2963 p3379 p3568 p4902 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73416 : p3568 ∨ p2295)
    (h73234 : p2299 ∨ p2177)
    (h51069 : (¬ p2254) ∨ (¬ p2299) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p2963) ∨ (¬ p3379) ∨ (¬ p3568) ∨ (¬ p4902))
    : p2331 ∨ (¬ p2373) ∨ (¬ p3379) ∨ (¬ p2254) ∨ (¬ p2406) ∨ p2295 ∨ p2177 ∨ (¬ p4902) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h51069 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step90974 (p2406 p2901 p2922 p2928 p4001 p4705 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h41940 : (¬ p2406) ∨ (¬ p2901) ∨ (¬ p2928) ∨ (¬ p4001) ∨ (¬ p4705))
    : (¬ p2901) ∨ (¬ p2406) ∨ (¬ p4705) ∨ (¬ p4001) ∨ p2922 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41940 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step90976 (p2406 p2563 p2922 p2928 p4001 p4555 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h52919 : (¬ p2406) ∨ (¬ p2563) ∨ (¬ p2928) ∨ (¬ p4001) ∨ (¬ p4555))
    : p2922 ∨ (¬ p2406) ∨ (¬ p4555) ∨ (¬ p4001) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h52919 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step90979 (p2406 p2493 p2499 p2860 p3096 p4885 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h60030 : (¬ p2406) ∨ (¬ p2499) ∨ (¬ p2860) ∨ (¬ p3096) ∨ (¬ p4885))
    : (¬ p2406) ∨ p2493 ∨ (¬ p3096) ∨ (¬ p4885) ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2493) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h60030 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step90985 (p2406 p2427 p2891 p3379 p3486 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h57476 : (¬ p2406) ∨ (¬ p2427) ∨ (¬ p3379) ∨ (¬ p3486))
    : (¬ p2427) ∨ p2891 ∨ (¬ p2406) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h57476 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90987 (p2406 p2427 p2493 p2499 p3096 p4558 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h60756 : (¬ p2406) ∨ (¬ p2427) ∨ (¬ p2499) ∨ (¬ p3096) ∨ (¬ p4558))
    : (¬ p2406) ∨ (¬ p2427) ∨ (¬ p3096) ∨ (¬ p4558) ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h60756 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step90989 (p2132 p2138 p2406 p3379 p3698 p4736 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h63254 : (¬ p2138) ∨ (¬ p2406) ∨ (¬ p3379) ∨ (¬ p3698) ∨ (¬ p4736))
    : (¬ p2406) ∨ (¬ p4736) ∨ (¬ p3698) ∨ p2132 ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63254 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step90993 (p2122 p2307 p2313 p2373 p2406 p2819 p3379 p4358 p4433 p5021 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73564 : p4358 ∨ p2819)
    (h49171 : (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p3379) ∨ (¬ p4358) ∨ (¬ p4433) ∨ (¬ p5021))
    : (¬ p2406) ∨ (¬ p2122) ∨ p2307 ∨ p2819 ∨ (¬ p5021) ∨ (¬ p2373) ∨ (¬ p4433) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49171 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step90995 (p2274 p2406 p2962 p3125 p3654 p3744 p4109 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h46137 : (¬ p2274) ∨ (¬ p2406) ∨ (¬ p2962) ∨ (¬ p3654) ∨ (¬ p3744) ∨ (¬ p4109))
    : (¬ p3654) ∨ p3125 ∨ (¬ p2274) ∨ (¬ p2962) ∨ (¬ p2406) ∨ (¬ p4109) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46137 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step90997 (p2406 p2850 p3379 p3422 p3684 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h45212 : (¬ p2406) ∨ (¬ p3379) ∨ (¬ p3422) ∨ (¬ p3684))
    : p2850 ∨ (¬ p2406) ∨ (¬ p3422) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45212 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step90998 (p2230 p2406 p2573 p2589 p3016 p3574 p4814 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73284 : p2589 ∨ p2230)
    (h51130 : (¬ p2406) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3574) ∨ (¬ p4814))
    : (¬ p2406) ∨ (¬ p2573) ∨ (¬ p4814) ∨ p3016 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51130 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91005 (p2406 p2417 p2922 p2928 p3246 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73320 : p2928 ∨ p2922)
    (h55575 : (¬ p2406) ∨ (¬ p2928) ∨ (¬ p3246) ∨ (¬ p4278))
    : p2417 ∨ (¬ p2406) ∨ p2922 ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h55575 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91006 (p2406 p2761 p3266 p3516 p4109 p4444 p4988 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h47362 : (¬ p2406) ∨ (¬ p2761) ∨ (¬ p3516) ∨ (¬ p4109) ∨ (¬ p4444) ∨ (¬ p4988))
    : (¬ p4988) ∨ p3266 ∨ (¬ p2406) ∨ (¬ p2761) ∨ (¬ p3516) ∨ (¬ p4109) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4988 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47362 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step91007 (p2406 p2563 p2608 p3379 p3954 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h64887 : (¬ p2406) ∨ (¬ p2563) ∨ (¬ p3379) ∨ (¬ p3954))
    : p2608 ∨ (¬ p2406) ∨ (¬ p2563) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h64887 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91013 (p2406 p2509 p2850 p3083 p3684 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h46517 : (¬ p2406) ∨ (¬ p2509) ∨ (¬ p3083) ∨ (¬ p3684))
    : (¬ p2406) ∨ (¬ p3083) ∨ (¬ p2509) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46517 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91014 (p2406 p2493 p2499 p2850 p3016 p3684 p4750 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73442 : p3684 ∨ p2850)
    (h63145 : (¬ p2406) ∨ (¬ p2499) ∨ (¬ p3016) ∨ (¬ p3684) ∨ (¬ p4750))
    : (¬ p2406) ∨ p2493 ∨ (¬ p4750) ∨ p2850 ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2493) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63145 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91015 (p2406 p2440 p2542 p4116 : Prop)
    (h73269 : (¬ p2440) ∨ (¬ p2542))
    (h6867 : (¬ p2406) ∨ p2542 ∨ (¬ p4116))
    : (¬ p4116) ∨ (¬ p2406) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4116 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2542) := (Or.elim h73269 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h6867 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step91018 (p2406 p2493 p2499 p2982 p3096 p5046 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h49804 : (¬ p2406) ∨ (¬ p2499) ∨ (¬ p2982) ∨ (¬ p3096) ∨ (¬ p5046))
    : (¬ p2406) ∨ (¬ p2982) ∨ p2493 ∨ (¬ p3096) ∨ (¬ p5046) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5046 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h49804 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step91023 (p2406 p2427 p3051 p3556 p3904 p5191 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h53151 : (¬ p2406) ∨ (¬ p2427) ∨ (¬ p3556) ∨ (¬ p3904) ∨ (¬ p5191))
    : (¬ p2427) ∨ (¬ p2406) ∨ (¬ p5191) ∨ (¬ p3904) ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h53151 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91024 (p2230 p2406 p2589 p2608 p3948 p4210 p4376 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h67005 : (¬ p2589) ∨ (¬ p4376) ∨ (¬ p2406) ∨ (¬ p3948) ∨ (¬ p4210) ∨ (¬ p2608))
    : (¬ p2608) ∨ (¬ p2406) ∨ (¬ p3948) ∨ (¬ p4376) ∨ (¬ p4210) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h67005 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step91025 (p2230 p2406 p2589 p2641 p2662 p4154 p4281 p4972 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73284 : p2589 ∨ p2230)
    (h41929 : (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2662) ∨ (¬ p4154) ∨ (¬ p4281) ∨ (¬ p4972))
    : (¬ p2406) ∨ p2641 ∨ (¬ p2662) ∨ (¬ p4972) ∨ p2230 ∨ (¬ p4281) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41929 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step91033 (p2230 p2406 p2417 p2589 p2922 p2928 p4108 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73320 : p2928 ∨ p2922)
    (h73284 : p2589 ∨ p2230)
    (h43546 : (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2928) ∨ (¬ p4108) ∨ (¬ p4278))
    : p2417 ∨ (¬ p2406) ∨ p2922 ∨ (¬ p4108) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43546 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step91034 (p2122 p2177 p2230 p2406 p2509 p2589 p2774 p4108 p4438 p4733 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h64054 : (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2406) ∨ (¬ p2509) ∨ (¬ p2589) ∨ (¬ p2774) ∨ (¬ p4108) ∨ (¬ p4438) ∨ (¬ p4733))
    : (¬ p2122) ∨ (¬ p2774) ∨ (¬ p2177) ∨ (¬ p4438) ∨ (¬ p4108) ∨ (¬ p4733) ∨ p2230 ∨ (¬ p2406) ∨ (¬ p2509) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h64054 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step91036 (p2187 p2230 p2406 p2493 p2499 p2589 p3096 p3989 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73502 : p3989 ∨ p2187)
    (h73284 : p2589 ∨ p2230)
    (h44149 : (¬ p2406) ∨ (¬ p2499) ∨ (¬ p2589) ∨ (¬ p3096) ∨ (¬ p3989))
    : (¬ p2406) ∨ p2493 ∨ p2187 ∨ p2230 ∨ (¬ p3096) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2493) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44149 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step91039 (p2406 p2493 p2499 p3573 p4355 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h31296 : (¬ p2406) ∨ (¬ p2499) ∨ (¬ p3573) ∨ (¬ p4355))
    : (¬ p4355) ∨ (¬ p2406) ∨ p2493 ∨ (¬ p3573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4355 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h31296 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step91042 (p2373 p2406 p2922 p2928 p4001 p4904 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h55300 : (¬ p2373) ∨ (¬ p2406) ∨ (¬ p2928) ∨ (¬ p4001) ∨ (¬ p4904))
    : p2922 ∨ (¬ p2406) ∨ (¬ p2373) ∨ (¬ p4001) ∨ (¬ p4904) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h55300 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step91043 (p2220 p2373 p2406 p3904 p4120 p5191 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h41409 : (¬ p2373) ∨ (¬ p2406) ∨ (¬ p3904) ∨ (¬ p4120) ∨ (¬ p5191))
    : (¬ p2373) ∨ p2220 ∨ (¬ p3904) ∨ (¬ p5191) ∨ (¬ p2406) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41409 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step91044 (p2363 p2373 p2383 p2387 p2406 p2459 p3379 p4347 p4902 p5021 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h73560 : p4347 ∨ p2363)
    (h48066 : (¬ p2373) ∨ (¬ p2387) ∨ (¬ p2406) ∨ (¬ p2459) ∨ (¬ p3379) ∨ (¬ p4347) ∨ (¬ p4902) ∨ (¬ p5021))
    : (¬ p2373) ∨ (¬ p2406) ∨ (¬ p4902) ∨ (¬ p3379) ∨ p2383 ∨ p2363 ∨ (¬ p2459) ∨ (¬ p5021) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h48066 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step91047 (p2406 p2608 p2850 p3379 p3684 p3954 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73442 : p3684 ∨ p2850)
    (h43900 : (¬ p2406) ∨ (¬ p3379) ∨ (¬ p3684) ∨ (¬ p3954))
    : (¬ p2406) ∨ p2608 ∨ p2850 ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43900 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91048 (p2406 p3032 p3379 p3399 p3740 p4366 p4644 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h50237 : (¬ p2406) ∨ (¬ p3032) ∨ (¬ p3379) ∨ (¬ p3740) ∨ (¬ p4366) ∨ (¬ p4644))
    : p3399 ∨ (¬ p3032) ∨ (¬ p3740) ∨ (¬ p3379) ∨ (¬ p2406) ∨ (¬ p4644) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h50237 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step91049 (p2406 p2437 p2493 p2499 p3016 p3742 p4644 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73260 : p2499 ∨ p2493)
    (h55168 : (¬ p2406) ∨ (¬ p2499) ∨ (¬ p3016) ∨ (¬ p3742) ∨ (¬ p4644))
    : (¬ p3016) ∨ p2437 ∨ p2493 ∨ (¬ p4644) ∨ (¬ p2406) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3016 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h55168 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step91050 (p2406 p2651 p2946 p2952 p3879 p4814 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h53969 : (¬ p2406) ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3879) ∨ (¬ p4814))
    : (¬ p2406) ∨ p2946 ∨ (¬ p4814) ∨ (¬ p2651) ∨ (¬ p3879) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h53969 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91051 (p2406 p2440 p2911 p2922 p2928 p3644 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73320 : p2928 ∨ p2922)
    (h47331 : (¬ p2406) ∨ (¬ p2440) ∨ (¬ p2928) ∨ (¬ p3644))
    : p2911 ∨ (¬ p2406) ∨ (¬ p2440) ∨ p2922 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47331 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91054 (p2249 p2406 p2440 p2651 p2657 p4281 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h51765 : (¬ p2249) ∨ (¬ p2406) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p4281))
    : (¬ p2406) ∨ (¬ p2249) ∨ (¬ p2440) ∨ p2651 ∨ (¬ p4281) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h51765 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step91056 (p2406 p2440 p2630 p2751 p2810 p4281 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h62992 : (¬ p2406) ∨ (¬ p2440) ∨ (¬ p2751) ∨ (¬ p2810) ∨ (¬ p4281))
    : (¬ p2406) ∨ p2630 ∨ (¬ p2751) ∨ (¬ p4281) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2630) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h62992 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step91057 (p2406 p2440 p2493 p2499 p2553 p2588 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73282 : p2588 ∨ p2553)
    (h45355 : (¬ p2406) ∨ (¬ p2440) ∨ (¬ p2499) ∨ (¬ p2588))
    : (¬ p2406) ∨ (¬ p2440) ∨ p2493 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45355 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step91059 (p2406 p2797 p2850 p3364 p3379 p3684 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h55730 : (¬ p2406) ∨ (¬ p2797) ∨ (¬ p3364) ∨ (¬ p3379) ∨ (¬ p3684))
    : (¬ p2406) ∨ (¬ p2797) ∨ p2850 ∨ (¬ p3364) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h55730 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step91060 (p2307 p2406 p2497 p2578 p3309 p3549 p4715 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h60021 : (¬ p2307) ∨ (¬ p2406) ∨ (¬ p2497) ∨ (¬ p2578) ∨ (¬ p3549) ∨ (¬ p4715))
    : (¬ p2406) ∨ (¬ p2307) ∨ (¬ p2497) ∨ p3309 ∨ (¬ p2578) ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60021 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step91061 (p2274 p2406 p2553 p2573 p2579 p2588 p3347 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73282 : p2588 ∨ p2553)
    (h45464 : (¬ p2274) ∨ (¬ p2406) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3347))
    : (¬ p2406) ∨ (¬ p2274) ∨ p2573 ∨ p2553 ∨ (¬ p3347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45464 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step91063 (p2406 p2573 p2579 p2850 p3016 p3347 p3684 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73442 : p3684 ∨ p2850)
    (h57986 : (¬ p2406) ∨ (¬ p2579) ∨ (¬ p3016) ∨ (¬ p3347) ∨ (¬ p3684))
    : (¬ p2406) ∨ (¬ p3016) ∨ p2573 ∨ (¬ p3347) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h57986 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step91066 (p2406 p3379 p3830 p3834 p4949 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h67178 : (¬ p3834) ∨ (¬ p4949) ∨ (¬ p3379) ∨ (¬ p2406))
    : p3830 ∨ (¬ p2406) ∨ (¬ p3379) ∨ (¬ p4949) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4949 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h67178 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step91067 (p2241 p2247 p2406 p2563 p3379 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h45079 : (¬ p2247) ∨ (¬ p2406) ∨ (¬ p2563) ∨ (¬ p3379))
    : p2241 ∨ (¬ p2406) ∨ (¬ p3379) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45079 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step91068 (p2406 p2440 p2608 p3379 p3954 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h44567 : (¬ p2406) ∨ (¬ p2440) ∨ (¬ p3379) ∨ (¬ p3954))
    : p2608 ∨ (¬ p2406) ∨ (¬ p3379) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h44567 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91069 (p2406 p2437 p2922 p2928 p3083 p4256 : Prop)
    (h73542 : p4256 ∨ p3083)
    (h73320 : p2928 ∨ p2922)
    (h46502 : (¬ p2406) ∨ (¬ p2437) ∨ (¬ p2928) ∨ (¬ p4256))
    : (¬ p2437) ∨ (¬ p2406) ∨ p3083 ∨ p2922 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46502 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91070 (p2230 p2406 p2589 p2662 p2996 p4281 p4650 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h41289 : (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2662) ∨ (¬ p2996) ∨ (¬ p4281) ∨ (¬ p4650))
    : (¬ p2406) ∨ (¬ p2996) ∨ (¬ p2662) ∨ (¬ p4650) ∨ p2230 ∨ (¬ p4281) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41289 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step91073 (p2156 p2406 p2493 p2499 p3096 p4539 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h50822 : (¬ p2156) ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p3096) ∨ (¬ p4539))
    : (¬ p2406) ∨ p2493 ∨ (¬ p4539) ∨ (¬ p2156) ∨ (¬ p3096) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2493) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4539 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h50822 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91076 (p2230 p2241 p2406 p2493 p2499 p2589 p4108 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h73260 : p2499 ∨ p2493)
    (h55409 : (¬ p2241) ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p2589) ∨ (¬ p4108))
    : (¬ p2241) ∨ (¬ p2406) ∨ p2230 ∨ p2493 ∨ (¬ p4108) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55409 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step91078 (p2254 p2331 p2363 p2406 p2668 p2963 p2982 p3324 p3379 p4347 p4450 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73338 : p2963 ∨ p2331)
    (h73386 : p3324 ∨ p2668)
    (h49080 : (¬ p2254) ∨ (¬ p2406) ∨ (¬ p2963) ∨ (¬ p2982) ∨ (¬ p3324) ∨ (¬ p3379) ∨ (¬ p4347) ∨ (¬ p4450))
    : (¬ p2982) ∨ p2363 ∨ (¬ p4450) ∨ p2331 ∨ (¬ p3379) ∨ (¬ p2254) ∨ (¬ p2406) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h49080 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step91081 (p2177 p2299 p2307 p2313 p2406 p2459 p2982 p3379 p4348 p4450 p5021 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73234 : p2299 ∨ p2177)
    (h73238 : p2313 ∨ p2307)
    (h54386 : (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2406) ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p4348) ∨ (¬ p4450) ∨ (¬ p5021))
    : p2459 ∨ p2177 ∨ (¬ p3379) ∨ (¬ p2982) ∨ (¬ p2406) ∨ p2307 ∨ (¬ p5021) ∨ (¬ p4450) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2177) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h54386 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step91086 (p2230 p2406 p2589 p3093 p3541 p4108 p4870 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h48770 : (¬ p2406) ∨ (¬ p2589) ∨ (¬ p3093) ∨ (¬ p3541) ∨ (¬ p4108) ∨ (¬ p4870))
    : (¬ p3093) ∨ (¬ p4870) ∨ (¬ p4108) ∨ p2230 ∨ (¬ p3541) ∨ (¬ p2406) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3093 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48770 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step91087 (p2363 p2406 p2493 p2496 p3073 p3573 p4261 p4371 p4608 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h73258 : p2496 ∨ p2493)
    (h66669 : (¬ p2496) ∨ (¬ p2406) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p3573) ∨ (¬ p2363) ∨ (¬ p4608))
    : p3073 ∨ (¬ p2406) ∨ (¬ p2363) ∨ (¬ p3573) ∨ p2493 ∨ (¬ p4371) ∨ (¬ p4608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p2496 := (Or.elim h73258 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h66669 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step91091 (p2363 p2406 p2509 p2528 p2534 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h57873 : (¬ p2363) ∨ (¬ p2406) ∨ (¬ p2509) ∨ (¬ p2534))
    : (¬ p2509) ∨ p2528 ∨ (¬ p2406) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h57873 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91092 (p2230 p2406 p2509 p2528 p2534 p2589 p4108 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73284 : p2589 ∨ p2230)
    (h52370 : (¬ p2406) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2589) ∨ (¬ p4108))
    : p2528 ∨ (¬ p4108) ∨ p2230 ∨ (¬ p2406) ∨ (¬ p2509) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52370 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step91094 (p2406 p2696 p2982 p3005 p3256 p3365 p3379 p3877 p4118 p4450 p4736 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73520 : p4118 ∨ p3256)
    (h73390 : p3365 ∨ p2696)
    (h50416 : (¬ p2406) ∨ (¬ p2982) ∨ (¬ p3365) ∨ (¬ p3379) ∨ (¬ p3877) ∨ (¬ p4118) ∨ (¬ p4450) ∨ (¬ p4736))
    : p3005 ∨ p3256 ∨ (¬ p4736) ∨ (¬ p4450) ∨ (¬ p2982) ∨ p2696 ∨ (¬ p3379) ∨ (¬ p2406) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h50416 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step91097 (p2383 p2387 p2406 p2982 p3266 p3322 p3379 p3461 p4191 p4450 p5021 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73246 : p2387 ∨ p2383)
    (h48235 : (¬ p2387) ∨ (¬ p2406) ∨ (¬ p2982) ∨ (¬ p3266) ∨ (¬ p3322) ∨ (¬ p3379) ∨ (¬ p4191) ∨ (¬ p4450) ∨ (¬ p5021))
    : p3461 ∨ (¬ p3266) ∨ (¬ p2982) ∨ (¬ p2406) ∨ (¬ p3379) ∨ (¬ p4450) ∨ (¬ p5021) ∨ (¬ p3322) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h48235 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step91101 (p2245 p2406 p3286 p3292 p3379 p4949 p5171 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h42148 : (¬ p2245) ∨ (¬ p2406) ∨ (¬ p3292) ∨ (¬ p3379) ∨ (¬ p4949) ∨ (¬ p5171))
    : (¬ p2245) ∨ p3286 ∨ (¬ p5171) ∨ (¬ p3379) ∨ (¬ p4949) ∨ (¬ p2406) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4949 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42148 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step91102 (p2177 p2341 p2396 p2406 p2982 p3379 p3551 p4107 p4395 p5210 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73514 : p4107 ∨ p2396)
    (h63305 : (¬ p2177) ∨ (¬ p2406) ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p3551) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p5210))
    : (¬ p2982) ∨ p2341 ∨ (¬ p2177) ∨ (¬ p2406) ∨ (¬ p5210) ∨ (¬ p4395) ∨ (¬ p3379) ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h63305 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step91104 (p2098 p2104 p2373 p2406 p2459 p3379 p3609 p4340 p4736 p4902 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h73204 : p2104 ∨ p2098)
    (h53382 : (¬ p2104) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p2459) ∨ (¬ p3379) ∨ (¬ p4340) ∨ (¬ p4736) ∨ (¬ p4902))
    : p3609 ∨ (¬ p2406) ∨ p2098 ∨ (¬ p4736) ∨ (¬ p2373) ∨ (¬ p2459) ∨ (¬ p4902) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h53382 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step91110 (p2406 p2870 p2922 p2928 p4001 p4885 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h49072 : (¬ p2406) ∨ (¬ p2870) ∨ (¬ p2928) ∨ (¬ p4001) ∨ (¬ p4885))
    : (¬ p2870) ∨ (¬ p2406) ∨ (¬ p4001) ∨ (¬ p4885) ∨ p2922 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49072 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step91111 (p2088 p2406 p2474 p2528 p3347 p3857 p4608 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h41322 : (¬ p2406) ∨ (¬ p2474) ∨ (¬ p2528) ∨ (¬ p3347) ∨ (¬ p3857) ∨ (¬ p4608))
    : (¬ p2406) ∨ (¬ p2528) ∨ (¬ p4608) ∨ (¬ p2474) ∨ p2088 ∨ (¬ p3347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2474 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41322 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step91113 (p2406 p3016 p3574 p3660 p4116 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h20004 : (¬ p2406) ∨ (¬ p3574) ∨ (¬ p3660) ∨ (¬ p4116))
    : (¬ p2406) ∨ (¬ p4116) ∨ p3016 ∨ (¬ p3660) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20004 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step91116 (p2187 p2352 p2406 p2493 p2499 p3956 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73500 : p3956 ∨ p2352)
    (h46901 : (¬ p2187) ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p3956))
    : p2493 ∨ (¬ p2406) ∨ p2352 ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2493) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46901 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step91125 (p2406 p2497 p3319 p3564 p4026 p4715 : Prop)
    (h73504 : p4026 ∨ p3319)
    (h49643 : (¬ p2406) ∨ (¬ p2497) ∨ (¬ p3564) ∨ (¬ p4026) ∨ (¬ p4715))
    : (¬ p3564) ∨ (¬ p2406) ∨ p3319 ∨ (¬ p4715) ∨ (¬ p2497) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h49643 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step91128 (p2406 p2608 p2982 p3379 p3954 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h43925 : (¬ p2406) ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p3954))
    : p2608 ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p2406) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h43925 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91129 (p2406 p2982 p3461 p3680 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h56500 : (¬ p2406) ∨ (¬ p2982) ∨ (¬ p3680) ∨ (¬ p4191))
    : (¬ p3680) ∨ p3461 ∨ (¬ p2406) ∨ (¬ p2982) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h56500 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91130 (p2406 p2761 p2982 p3379 p3461 p3654 p3946 p4191 p4395 p5021 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73492 : p3946 ∨ p3654)
    (h42526 : (¬ p2406) ∨ (¬ p2761) ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p3946) ∨ (¬ p4191) ∨ (¬ p4395) ∨ (¬ p5021))
    : p3461 ∨ (¬ p2761) ∨ (¬ p3379) ∨ p3654 ∨ (¬ p2982) ∨ (¬ p2406) ∨ (¬ p5021) ∨ (¬ p4395) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42526 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step91131 (p2241 p2247 p2406 p2440 p3379 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h54220 : (¬ p2247) ∨ (¬ p2406) ∨ (¬ p2440) ∨ (¬ p3379))
    : p2241 ∨ (¬ p2406) ∨ (¬ p3379) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h54220 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step91138 (p2406 p2911 p2926 p3527 p3548 p4644 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h49592 : (¬ p2406) ∨ (¬ p2911) ∨ (¬ p2926) ∨ (¬ p3548) ∨ (¬ p4644))
    : p3527 ∨ (¬ p2911) ∨ (¬ p4644) ∨ (¬ p2406) ∨ (¬ p2926) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2926 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49592 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91149 (p2406 p2437 p2850 p2922 p2928 p3684 p4750 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73442 : p3684 ∨ p2850)
    (h50808 : (¬ p2406) ∨ (¬ p2437) ∨ (¬ p2928) ∨ (¬ p3684) ∨ (¬ p4750))
    : (¬ p2406) ∨ (¬ p2437) ∨ p2922 ∨ (¬ p4750) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50808 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step91150 (p2373 p2406 p2437 p2922 p2928 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h45676 : (¬ p2373) ∨ (¬ p2406) ∨ (¬ p2437) ∨ (¬ p2928))
    : (¬ p2437) ∨ (¬ p2406) ∨ p2922 ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45676 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91157 (p2396 p4025 p5845 : Prop)
    (h74137 : p2396 ∨ (¬ p5845))
    (h12066 : p4025 ∨ p5845)
    : p4025 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4025) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5845) := (Or.elim h74137 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12066 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step91159 (p2396 p4623 p5846 : Prop)
    (h74139 : (¬ p2396) ∨ (¬ p5846))
    (h12070 : p4623 ∨ p5846)
    : p4623 ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4623) := (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5846) := (Or.elim h74139 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12070 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step91160 (p2396 p4187 p5846 : Prop)
    (h74139 : (¬ p2396) ∨ (¬ p5846))
    (h12071 : p4187 ∨ p5846)
    : p4187 ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4187) := (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5846) := (Or.elim h74139 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12071 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step91164 (p2630 p4343 p5890 : Prop)
    (h74193 : p2630 ∨ (¬ p5890))
    (h12325 : p4343 ∨ p5890)
    : p4343 ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4343) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2630) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5890) := (Or.elim h74193 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12325 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step91165 (p2696 p2811 p5902 : Prop)
    (h74209 : p2696 ∨ (¬ p5902))
    (h12394 : p2811 ∨ p5902)
    : p2811 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2811) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5902) := (Or.elim h74209 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12394 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step91166 (p2696 p4236 p5902 : Prop)
    (h74209 : p2696 ∨ (¬ p5902))
    (h12397 : p4236 ∨ p5902)
    : p4236 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4236) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5902) := (Or.elim h74209 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12397 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step91169 (p2911 p4186 p5950 : Prop)
    (h74273 : p2911 ∨ (¬ p5950))
    (h12683 : p4186 ∨ p5950)
    : p4186 ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4186) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2911) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5950) := (Or.elim h74273 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12683 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step91178 (p2143 p2156 p2870 p3646 p4204 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h20402 : (¬ p2143) ∨ (¬ p2870) ∨ (¬ p3646) ∨ (¬ p4204))
    : (¬ p2870) ∨ (¬ p4204) ∨ (¬ p2143) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h20402 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step91181 (p2143 p2427 p2839 p3051 p3367 p3556 p3583 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73414 : p3556 ∨ p3051)
    (h45323 : (¬ p2143) ∨ (¬ p2427) ∨ (¬ p3367) ∨ (¬ p3556) ∨ (¬ p3583))
    : (¬ p3367) ∨ p2839 ∨ (¬ p2427) ∨ p3051 ∨ (¬ p2143) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45323 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step91182 (p2143 p2737 p2839 p2881 p3051 p3556 p3570 p3583 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73424 : p3583 ∨ p2839)
    (h73418 : p3570 ∨ p2881)
    (h63259 : (¬ p2143) ∨ (¬ p2737) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3583))
    : p3051 ∨ (¬ p2737) ∨ (¬ p2143) ∨ p2839 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63259 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step91190 (p2143 p2187 p2274 p2307 p2313 p2839 p3583 p3989 p4198 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73424 : p3583 ∨ p2839)
    (h73502 : p3989 ∨ p2187)
    (h54346 : (¬ p2143) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p3583) ∨ (¬ p3989) ∨ (¬ p4198))
    : p2307 ∨ (¬ p4198) ∨ (¬ p2143) ∨ (¬ p2274) ∨ p2839 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2307) := (fun h => hn (Or.inl h));
    let u1 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u8 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h54346 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step91197 (p2143 p2264 p2696 p2742 p2839 p2996 p3027 p3051 p3246 p3556 p3583 p3690 p4666 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73414 : p3556 ∨ p3051)
    (h73340 : p3027 ∨ p2996)
    (h73424 : p3583 ∨ p2839)
    (h71907 : (¬ p3583) ∨ (¬ p3690) ∨ (¬ p2742) ∨ (¬ p2696) ∨ (¬ p3556) ∨ (¬ p4666) ∨ (¬ p2143) ∨ (¬ p2264) ∨ (¬ p3027))
    : (¬ p2742) ∨ p3246 ∨ (¬ p2264) ∨ p3051 ∨ p2996 ∨ (¬ p2696) ∨ (¬ p4666) ∨ (¬ p2143) ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2742 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h71907 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u11)))))))))))))))))))

theorem step91198 (p2143 p2156 p2707 p2839 p3583 p3646 p4344 p4558 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73436 : p3646 ∨ p2156)
    (h49314 : (¬ p2143) ∨ (¬ p2707) ∨ (¬ p3583) ∨ (¬ p3646) ∨ (¬ p4344) ∨ (¬ p4558))
    : (¬ p2707) ∨ p2839 ∨ p2156 ∨ (¬ p2143) ∨ (¬ p4344) ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h49314 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step91199 (p2143 p2449 p2696 p2839 p2881 p3005 p3051 p3556 p3570 p3583 p3919 p4668 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73418 : p3570 ∨ p2881)
    (h73424 : p3583 ∨ p2839)
    (h71908 : (¬ p2449) ∨ (¬ p3005) ∨ (¬ p4668) ∨ (¬ p3919) ∨ (¬ p2696) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3583) ∨ (¬ p2143))
    : (¬ p2449) ∨ p3051 ∨ p2881 ∨ (¬ p3919) ∨ (¬ p4668) ∨ p2839 ∨ (¬ p3005) ∨ (¬ p2143) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h71908 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step91203 (p2143 p2156 p2696 p2742 p2839 p3125 p3189 p3256 p3583 p3646 p3744 p4604 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73454 : p3744 ∨ p3125)
    (h73424 : p3583 ∨ p2839)
    (h71910 : (¬ p3583) ∨ (¬ p2143) ∨ (¬ p3744) ∨ (¬ p2696) ∨ (¬ p3646) ∨ (¬ p4604) ∨ (¬ p3256) ∨ (¬ p2742) ∨ (¬ p3189))
    : (¬ p3189) ∨ p2156 ∨ (¬ p2143) ∨ p3125 ∨ p2839 ∨ (¬ p4604) ∨ (¬ p2742) ∨ (¬ p3256) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h71910 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step91210 (p2143 p2274 p2284 p2737 p2839 p2951 p3097 p3583 p3952 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73496 : p3952 ∨ p2284)
    (h73424 : p3583 ∨ p2839)
    (h46504 : (¬ p2143) ∨ (¬ p2737) ∨ (¬ p2951) ∨ (¬ p3097) ∨ (¬ p3583) ∨ (¬ p3952))
    : (¬ p2737) ∨ p2274 ∨ (¬ p2143) ∨ p2284 ∨ p2839 ∨ (¬ p2951) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46504 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step91212 (p2143 p2493 p2499 p2934 p3516 p3631 p3695 p3821 p4715 p4984 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73260 : p2499 ∨ p2493)
    (h51527 : (¬ p2143) ∨ (¬ p2499) ∨ (¬ p2934) ∨ (¬ p3631) ∨ (¬ p3695) ∨ (¬ p3821) ∨ (¬ p4715) ∨ (¬ p4984))
    : (¬ p3631) ∨ (¬ p3695) ∨ p3516 ∨ (¬ p2934) ∨ (¬ p4984) ∨ p2493 ∨ (¬ p2143) ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2934 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h51527 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step91213 (p2143 p2220 p2373 p2563 p2839 p3583 p4110 p4120 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h73516 : p4110 ∨ p2563)
    (h73522 : p4120 ∨ p2220)
    (h43971 : (¬ p2143) ∨ (¬ p2373) ∨ (¬ p3583) ∨ (¬ p4110) ∨ (¬ p4120))
    : (¬ p2373) ∨ (¬ p2143) ∨ p2839 ∨ p2563 ∨ p2220 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43971 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step91216 (p2143 p2177 p2839 p2881 p3051 p3556 p3570 p3583 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73424 : p3583 ∨ p2839)
    (h73414 : p3556 ∨ p3051)
    (h46621 : (¬ p2143) ∨ (¬ p2177) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3583))
    : p2881 ∨ p2839 ∨ (¬ p2143) ∨ p3051 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46621 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step91218 (p2143 p2839 p3461 p3583 p4032 p4322 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h56873 : (¬ p2143) ∨ (¬ p3461) ∨ (¬ p3583) ∨ (¬ p4032) ∨ (¬ p4322))
    : (¬ p4322) ∨ (¬ p3461) ∨ (¬ p2143) ∨ (¬ p4032) ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56873 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step91220 (p2143 p2459 p2696 p2819 p2829 p3051 p3146 p3365 p3366 p3556 p3692 p4119 p4133 p5052 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73390 : p3365 ∨ p2696)
    (h73414 : p3556 ∨ p3051)
    (h63689 : (¬ p2143) ∨ (¬ p2459) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3556) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4133) ∨ (¬ p5052))
    : p3146 ∨ (¬ p3366) ∨ (¬ p5052) ∨ (¬ p2819) ∨ (¬ p4133) ∨ (¬ p4119) ∨ (¬ p2143) ∨ (¬ p2459) ∨ (¬ p2829) ∨ p2696 ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5052 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u13 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h63689 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u4))) (fun r9 => (False.elim (r9 u2)))))))))))))))))))))))

theorem step91222 (p2143 p2220 p2493 p2598 p2839 p3146 p3564 p3583 p3590 p3692 p4120 p4330 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73522 : p4120 ∨ p2220)
    (h73424 : p3583 ∨ p2839)
    (h71914 : (¬ p3590) ∨ (¬ p2493) ∨ (¬ p2143) ∨ (¬ p3564) ∨ (¬ p2598) ∨ (¬ p3583) ∨ (¬ p4330) ∨ (¬ p3692) ∨ (¬ p4120))
    : p3146 ∨ (¬ p3564) ∨ p2220 ∨ (¬ p2598) ∨ (¬ p2143) ∨ (¬ p2493) ∨ (¬ p4330) ∨ (¬ p3590) ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h71914 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u10)))))))))))))))))))

theorem step91230 (p2143 p2156 p2192 p2737 p3646 p4515 : Prop)
    (h73612 : p4515 ∨ (¬ p2192))
    (h73436 : p3646 ∨ p2156)
    (h66780 : p2737 ∨ (¬ p4515) ∨ (¬ p2143) ∨ (¬ p3646))
    : (¬ p2192) ∨ p2737 ∨ (¬ p2143) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4515 := (Or.elim h73612 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h66780 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step91231 (p2143 p2220 p2737 p2839 p3146 p3583 p3692 p4120 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73522 : p4120 ∨ p2220)
    (h73424 : p3583 ∨ p2839)
    (h46871 : (¬ p2143) ∨ (¬ p2737) ∨ (¬ p3583) ∨ (¬ p3692) ∨ (¬ p4120))
    : (¬ p2737) ∨ p3146 ∨ p2220 ∨ p2839 ∨ (¬ p2143) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46871 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step91232 (p2143 p2220 p2839 p3146 p3266 p3583 p3692 p4120 p4444 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73424 : p3583 ∨ p2839)
    (h73580 : p4444 ∨ p3266)
    (h73522 : p4120 ∨ p2220)
    (h45549 : (¬ p2143) ∨ (¬ p3583) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4444))
    : p3146 ∨ p2839 ∨ (¬ p2143) ∨ p3266 ∨ p2220 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45549 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step91239 (p2166 p2210 p3093 p3591 p3918 p4428 p4509 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h64915 : (¬ p2166) ∨ (¬ p2210) ∨ (¬ p3591) ∨ (¬ p3918) ∨ (¬ p4428) ∨ (¬ p4509))
    : (¬ p4428) ∨ (¬ p3918) ∨ p3093 ∨ (¬ p2210) ∨ (¬ p4509) ∨ (¬ p2166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4428 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3918 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h64915 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step91243 (p2210 p2373 p3093 p3591 p3918 p4210 p4428 p4509 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h64932 : (¬ p2210) ∨ (¬ p2373) ∨ (¬ p3591) ∨ (¬ p3918) ∨ (¬ p4210) ∨ (¬ p4428) ∨ (¬ p4509))
    : p3093 ∨ (¬ p3918) ∨ (¬ p2210) ∨ (¬ p4428) ∨ (¬ p2373) ∨ (¬ p4509) ∨ (¬ p4210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p3918 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4428 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h64932 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step91249 (p2449 p3156 p3426 p3434 p3947 p4386 p4428 p4509 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h64474 : (¬ p3156) ∨ (¬ p3426) ∨ (¬ p3434) ∨ (¬ p3947) ∨ (¬ p4386) ∨ (¬ p4428) ∨ (¬ p4509))
    : (¬ p3434) ∨ p2449 ∨ (¬ p3156) ∨ (¬ p4386) ∨ (¬ p4509) ∨ (¬ p4428) ∨ (¬ p3426) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4428 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h64474 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step91251 (p3083 p4346 p5978 : Prop)
    (h74307 : (¬ p3083) ∨ (¬ p5978))
    (h12858 : p4346 ∨ p5978)
    : p4346 ∨ (¬ p3083) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4346) := (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5978) := (Or.elim h74307 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12858 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step91252 (p2132 p2696 p2797 p3365 p4195 p4700 p4972 p5051 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73390 : p3365 ∨ p2696)
    (h56869 : (¬ p2132) ∨ (¬ p3365) ∨ (¬ p4195) ∨ (¬ p4700) ∨ (¬ p4972) ∨ (¬ p5051))
    : (¬ p2132) ∨ p2797 ∨ (¬ p5051) ∨ (¬ p4972) ∨ p2696 ∨ (¬ p4700) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56869 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step91255 (p2140 p2341 p2870 p2881 p3551 p4984 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h50647 : (¬ p2140) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3551) ∨ (¬ p4984))
    : (¬ p2140) ∨ (¬ p4984) ∨ (¬ p2881) ∨ p2341 ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2140 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50647 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step91258 (p2284 p3125 p3483 p3744 p3952 p3985 p5053 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73454 : p3744 ∨ p3125)
    (h56492 : (¬ p3483) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p3985) ∨ (¬ p5053))
    : (¬ p3483) ∨ p2284 ∨ (¬ p3985) ∨ (¬ p5053) ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3985 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56492 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step91259 (p2807 p2870 p2946 p3414 p3699 p5053 : Prop)
    (h73392 : p3414 ∨ p2807)
    (h56425 : (¬ p2870) ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3699) ∨ (¬ p5053))
    : (¬ p2870) ∨ (¬ p3699) ∨ (¬ p5053) ∨ (¬ p2946) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3699 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56425 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91261 (p2122 p2307 p2313 p2386 p2850 p3684 p4375 p4717 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73442 : p3684 ∨ p2850)
    (h42485 : (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p3684) ∨ (¬ p4375) ∨ (¬ p4717))
    : p2307 ∨ (¬ p2122) ∨ (¬ p4717) ∨ p2850 ∨ (¬ p2386) ∨ (¬ p4375) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2307) := (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42485 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step91264 (p2774 p2780 p3366 p3367 p4375 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h20303 : (¬ p2780) ∨ (¬ p3366) ∨ (¬ p3367) ∨ (¬ p4375))
    : p2774 ∨ (¬ p4375) ∨ (¬ p3367) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2774) := (fun h => hn (Or.inl h));
    let u1 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h20303 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step91265 (p2437 p3426 p3434 p3516 p3742 p3821 p4279 p4375 p4753 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73452 : p3742 ∨ p2437)
    (h42359 : (¬ p3426) ∨ (¬ p3434) ∨ (¬ p3742) ∨ (¬ p3821) ∨ (¬ p4279) ∨ (¬ p4375) ∨ (¬ p4753))
    : p3516 ∨ (¬ p3434) ∨ (¬ p4375) ∨ p2437 ∨ (¬ p3426) ∨ (¬ p4279) ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4279 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42359 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step91266 (p2352 p2437 p2819 p3201 p3876 p3956 p4375 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73500 : p3956 ∨ p2352)
    (h62593 : (¬ p2437) ∨ (¬ p2819) ∨ (¬ p3876) ∨ (¬ p3956) ∨ (¬ p4375))
    : (¬ p2819) ∨ p3201 ∨ p2352 ∨ (¬ p2437) ∨ (¬ p4375) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h62593 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step91269 (p2383 p2387 p2785 p2819 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h6268 : (¬ p2387) ∨ (¬ p2785) ∨ (¬ p2819))
    : (¬ p2819) ∨ p2383 ∨ (¬ p2785) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2383) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h6268 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u0)))))))

theorem step91273 (p2307 p2313 p2553 p2737 p2785 p2829 p3688 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73444 : p3688 ∨ p2829)
    (h62188 : (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2737) ∨ (¬ p2785) ∨ (¬ p3688))
    : p2307 ∨ p2829 ∨ (¬ p2785) ∨ (¬ p2553) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2307) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h62188 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step91275 (p2707 p2785 p2829 p3654 p3688 p3946 p4475 p4620 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h73492 : p3946 ∨ p3654)
    (h59437 : (¬ p2707) ∨ (¬ p2785) ∨ (¬ p3688) ∨ (¬ p3946) ∨ (¬ p4475) ∨ (¬ p4620))
    : p2829 ∨ (¬ p2707) ∨ (¬ p4475) ∨ p3654 ∨ (¬ p4620) ∨ (¬ p2785) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h59437 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step91278 (p2295 p2553 p2737 p2785 p2829 p3567 p3568 p3688 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73444 : p3688 ∨ p2829)
    (h62187 : (¬ p2553) ∨ (¬ p2737) ∨ (¬ p2785) ∨ (¬ p3567) ∨ (¬ p3568) ∨ (¬ p3688))
    : (¬ p3567) ∨ (¬ p2553) ∨ (¬ p2737) ∨ p2295 ∨ p2829 ∨ (¬ p2785) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3567 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62187 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step91280 (p2122 p2785 p3115 p3156 p3497 p3654 p3946 p5045 : Prop)
    (h73492 : p3946 ∨ p3654)
    (h73400 : p3497 ∨ p3156)
    (h46909 : (¬ p2122) ∨ (¬ p2785) ∨ (¬ p3115) ∨ (¬ p3497) ∨ (¬ p3946) ∨ (¬ p5045))
    : (¬ p3115) ∨ p3654 ∨ p3156 ∨ (¬ p5045) ∨ (¬ p2122) ∨ (¬ p2785) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3654) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46909 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step91284 (p3319 p3322 p3923 p4026 : Prop)
    (h73503 : (¬ p3319) ∨ (¬ p4026))
    (h37641 : (¬ p3322) ∨ (¬ p3923) ∨ p4026)
    : (¬ p3319) ∨ (¬ p3322) ∨ (¬ p3923) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4026) := (Or.elim h73503 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    (Or.elim h37641 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u3 r1)))))))

theorem step91287 (p2177 p2299 p2553 p2588 p3564 p4623 p4668 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h73282 : p2588 ∨ p2553)
    (h57898 : (¬ p2299) ∨ (¬ p2588) ∨ (¬ p3564) ∨ (¬ p4623) ∨ (¬ p4668))
    : (¬ p3564) ∨ (¬ p4623) ∨ (¬ p4668) ∨ p2177 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4623 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h57898 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91291 (p2274 p2396 p2417 p3581 p3958 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h51860 : (¬ p2274) ∨ (¬ p2396) ∨ (¬ p3581) ∨ (¬ p3958) ∨ (¬ p4278))
    : (¬ p2396) ∨ p2417 ∨ (¬ p2274) ∨ (¬ p3581) ∨ (¬ p3958) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h51860 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step91293 (p2352 p2911 p3550 p3581 p3644 p3956 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73499 : (¬ p2352) ∨ (¬ p3956))
    (h33448 : (¬ p3550) ∨ (¬ p3581) ∨ (¬ p3644) ∨ p3956)
    : p2911 ∨ (¬ p2352) ∨ (¬ p3581) ∨ (¬ p3550) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : (¬ p3956) := (Or.elim h73499 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h33448 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (u5 r2)))))))))

theorem step91294 (p2177 p2274 p2911 p3581 p3644 p3958 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h60360 : (¬ p2177) ∨ (¬ p2274) ∨ (¬ p3581) ∨ (¬ p3644) ∨ (¬ p3958))
    : p2911 ∨ (¬ p2274) ∨ (¬ p2177) ∨ (¬ p3958) ∨ (¬ p3581) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h60360 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step91295 (p2417 p2449 p2995 p3156 p3497 p3581 p4203 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73400 : p3497 ∨ p3156)
    (h69526 : (¬ p3497) ∨ (¬ p4278) ∨ (¬ p4203) ∨ (¬ p2449) ∨ (¬ p3581) ∨ (¬ p2995))
    : p2417 ∨ (¬ p2449) ∨ p3156 ∨ (¬ p3581) ∨ (¬ p4203) ∨ (¬ p2995) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h69526 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step91299 (p2274 p2396 p3434 p3581 p3658 p3958 p4324 : Prop)
    (h73556 : p4324 ∨ p3434)
    (h57703 : (¬ p2274) ∨ (¬ p2396) ∨ (¬ p3581) ∨ (¬ p3658) ∨ (¬ p3958) ∨ (¬ p4324))
    : (¬ p2396) ∨ p3434 ∨ (¬ p3581) ∨ (¬ p3958) ∨ (¬ p2274) ∨ (¬ p3658) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3434) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3658 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h57703 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step91300 (p2177 p2311 p2341 p2386 p2396 p3016 p3551 p3574 p4107 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73422 : p3574 ∨ p3016)
    (h73514 : p4107 ∨ p2396)
    (h61372 : (¬ p2177) ∨ (¬ p2311) ∨ (¬ p2386) ∨ (¬ p3551) ∨ (¬ p3574) ∨ (¬ p4107))
    : p2341 ∨ (¬ p2386) ∨ p3016 ∨ (¬ p2177) ∨ (¬ p2311) ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h61372 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u8)))))))))))))

theorem step91301 (p2177 p2299 p2307 p2313 p2386 p2459 p3016 p3574 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73234 : p2299 ∨ p2177)
    (h73238 : p2313 ∨ p2307)
    (h73422 : p3574 ∨ p3016)
    (h59709 : (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p3574) ∨ (¬ p4348))
    : p2459 ∨ p2177 ∨ (¬ p2386) ∨ p2307 ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2177) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h59709 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step91302 (p2383 p2386 p2387 p3564 p4345 p5118 p5580 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h49664 : (¬ p2386) ∨ (¬ p2387) ∨ (¬ p3564) ∨ (¬ p4345) ∨ (¬ p5118) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p5118) ∨ (¬ p3564) ∨ (¬ p2386) ∨ (¬ p4345) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4345 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h49664 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step91303 (p2307 p2313 p2386 p2553 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h15355 : (¬ p2313) ∨ (¬ p2386) ∨ (¬ p2553))
    : p2307 ∨ (¬ p2553) ∨ (¬ p2386) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2307) := (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h15355 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u1)))))))

theorem step91305 (p2352 p2383 p2386 p2387 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h2909 : (¬ p2352) ∨ (¬ p2386) ∨ (¬ p2387))
    : (¬ p2352) ∨ (¬ p2386) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h2909 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step91306 (p2187 p2274 p2383 p2386 p2387 p2493 p2499 p3097 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73246 : p2387 ∨ p2383)
    (h73260 : p2499 ∨ p2493)
    (h43108 : (¬ p2187) ∨ (¬ p2386) ∨ (¬ p2387) ∨ (¬ p2499) ∨ (¬ p3097))
    : p2274 ∨ (¬ p2187) ∨ (¬ p2386) ∨ p2383 ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43108 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step91309 (p2553 p2588 p3016 p3343 p3574 p4331 p4624 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73282 : p2588 ∨ p2553)
    (h62001 : (¬ p2588) ∨ (¬ p3343) ∨ (¬ p3574) ∨ (¬ p4331) ∨ (¬ p4624))
    : (¬ p4331) ∨ (¬ p3343) ∨ p3016 ∨ (¬ p4624) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4624 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62001 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step91310 (p2274 p2440 p3125 p3343 p3744 p4331 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h55818 : (¬ p2274) ∨ (¬ p2440) ∨ (¬ p3343) ∨ (¬ p3744) ∨ (¬ p4331))
    : (¬ p3343) ∨ (¬ p4331) ∨ (¬ p2274) ∨ (¬ p2440) ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55818 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step91312 (p2352 p3276 p3461 p3956 p4191 p4422 p4603 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73500 : p3956 ∨ p2352)
    (h56830 : (¬ p3276) ∨ (¬ p3956) ∨ (¬ p4191) ∨ (¬ p4422) ∨ (¬ p4603))
    : p3461 ∨ (¬ p3276) ∨ p2352 ∨ (¬ p4603) ∨ (¬ p4422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4603 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h56830 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step91315 (p2982 p4946 p4949 : Prop)
    (h73844 : p4946 ∨ p2982)
    (h8224 : (¬ p4946) ∨ p4949)
    : p2982 ∨ p4949 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4949) := (fun h => hn (Or.inr h));
    let u2 : p4946 := (Or.elim h73844 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h8224 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step91321 (p2761 p3399 p3707 p3830 p3834 p4321 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h73474 : p3834 ∨ p3830)
    (h47807 : (¬ p2761) ∨ (¬ p3399) ∨ (¬ p3834) ∨ (¬ p4321))
    : p3707 ∨ p3830 ∨ (¬ p2761) ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47807 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91322 (p3399 p3830 p3834 p5363 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h30481 : (¬ p3399) ∨ (¬ p3834) ∨ (¬ p5363))
    : p3830 ∨ (¬ p5363) ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p5363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h30481 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step91323 (p3246 p3399 p3830 p3834 p4911 p5358 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h42004 : (¬ p3246) ∨ (¬ p3399) ∨ (¬ p3834) ∨ (¬ p4911) ∨ (¬ p5358))
    : (¬ p5358) ∨ p3830 ∨ (¬ p3246) ∨ (¬ p4911) ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5358 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42004 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step91324 (p2417 p2930 p3399 p3830 p3834 p5358 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h42141 : (¬ p2417) ∨ (¬ p2930) ∨ (¬ p3399) ∨ (¬ p3834) ∨ (¬ p5358))
    : p3830 ∨ (¬ p2417) ∨ (¬ p3399) ∨ (¬ p5358) ∨ (¬ p2930) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2930 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42141 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step91328 (p2608 p3266 p3830 p3834 p3847 p5284 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h55687 : (¬ p2608) ∨ (¬ p3266) ∨ (¬ p3834) ∨ (¬ p3847) ∨ (¬ p5284))
    : (¬ p5284) ∨ p3830 ∨ (¬ p3266) ∨ (¬ p3847) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3847 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h55687 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step91329 (p2608 p2761 p3707 p3830 p3834 p4321 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h73474 : p3834 ∨ p3830)
    (h45833 : (¬ p2608) ∨ (¬ p2761) ∨ (¬ p3834) ∨ (¬ p4321))
    : p3707 ∨ p3830 ∨ (¬ p2761) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45833 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91330 (p2246 p2264 p2608 p2744 p2807 p3707 p3830 p3834 p3941 p4321 p5119 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h73474 : p3834 ∨ p3830)
    (h52793 : (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2807) ∨ (¬ p3834) ∨ (¬ p3941) ∨ (¬ p4321) ∨ (¬ p5119))
    : p3707 ∨ (¬ p2246) ∨ (¬ p2807) ∨ (¬ p2744) ∨ (¬ p2608) ∨ (¬ p3941) ∨ (¬ p5119) ∨ p3830 ∨ (¬ p2264) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h52793 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step91332 (p2192 p2210 p3830 p3834 p4388 p5043 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h61033 : (¬ p2192) ∨ (¬ p2210) ∨ (¬ p3834) ∨ (¬ p4388) ∨ (¬ p5043))
    : (¬ p4388) ∨ p3830 ∨ (¬ p5043) ∨ (¬ p2192) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4388 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h61033 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91334 (p3093 p3323 p3830 p3834 p4024 p4843 p5148 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h51541 : (¬ p3093) ∨ (¬ p3323) ∨ (¬ p3834) ∨ (¬ p4024) ∨ (¬ p4843) ∨ (¬ p5148))
    : p3830 ∨ (¬ p5148) ∨ (¬ p4843) ∨ (¬ p4024) ∨ (¬ p3323) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p5148 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4843 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4024 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h51541 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u1)))))))))))))

end ElevenRUP
